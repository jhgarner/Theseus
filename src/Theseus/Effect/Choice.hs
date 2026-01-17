{-# LANGUAGE QuantifiedConstraints #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Theseus.Effect.Choice (
  Choice (Empty, Choose),
  runChoice,
  Collect (Collect),
  runCollect,
  collect,
) where

import Control.Applicative
import Control.Monad
import Control.Monad.Identity
import Theseus.Eff

-- # Choice

-- Choice is probably the most complicated effect in Theseus. It's first order,
-- but it requires complicated control flow and changes the output. Take a look
-- at Error first to understand the control flow operations.

-- | This is the `ControlFlow` that `Choice` will use. There's the `Thrown`
-- control flow that handles 0 threads of computation, `IdentityCf` that
-- handles 1, and `MaybeCf` that handles 0 or 1. `Many` handles 0 or more
-- threads of computation.
data Many eff m a where
  -- So the way `Many` works is it collects computations, but waits to dispatch
  -- them to multiple "threads" (I'm using threads in a vague sense. It does
  -- not actually run multiple Haskell or CPU threads). When another
  -- interpreter needs to run, it runs all the threads independently, joins
  -- them together, then hands the result to to interpreter. To run all the
  -- threads separately, it needs to be able to intercept the `Choice`
  -- operations so they go to thread specific handlers. That means running the
  -- `Choice` interpreter while interpreting other stuff.
  Many ::
    -- While running the `ControlFlow`, the `ef` parameter might change. We
    -- need to track that ef remains compatible with our thread specific
    -- `Choice` interpreters. To do that we need to make sure lists are still
    -- valid wrappers and that all the other wrappers will be `Traversable`.
    [] `IsoSome` ef ->
    ef `Implies` Traversable ->
    -- These are the current values across all our threads of computation.
    Eff ef es [a] ->
    -- This is the operation we'd like to run on each thread.
    (a -> Eff ef es b) ->
    Many Choice (Eff ef es) b

deriving instance Functor (Many eff m)

instance ControlFlow Many Traversable where
  Many listIso travProof start go `cfApply` fa = Many listIso travProof start ((<*> fa) . go)
  Many listIso travProof start go `cfBind` afb = Many listIso travProof start (go >=> afb)
  cfMap efToOut implication handler (Many listIso _ start go) = Many (isoImplying listIso efToOut) implication (handler start) (handler . go)

  -- Most `Choice` implementations are depth first. They run one thread to
  -- completion, then they run the next. The problem with depth first is that
  -- it causes things like `State` to constantly go in and out of scope
  -- creating the "duplicate the world" semantics that are popular.
  --
  -- Theseus adopts a breadth first approach. We run all the threads in
  -- parallel. That means handlers aren't constantly going in and out of scope
  -- because all the threads will join before the interpreter goes out of
  -- scope.
  cfRun imply@(Implies go) handler many@(Many listIso _ _ _) = Many listIso imply newStart pure
   where
    -- We require `Traversable` because we need to know how many threads made
    -- it past the other interpreter.
    newStart = go \(Iso lr rl) -> fmap (fmap rl . sequenceA . lr) $ handler $ runMany many

-- There we go! That's how Theseus handles nondeterminism while avoiding the
-- handler ordering problems.

-- | Represents Nondeterminism kind of like what ListT does. You should use the
-- `Alternative` operations to send `Choice` effects.
data Choice :: Effect where
  -- Do these constraints leak unfortunate implementation details? Yes. I don't
  -- know how to get rid of them though.
  Empty :: (ef [], ef `IsAtLeast` Traversable) => Choice (Eff ef es) a
  Choose :: (ef [], ef `IsAtLeast` Traversable) => Choice (Eff ef es) Bool

-- | Runs a choice that causes all other effects to act globally over all the
-- threads.
runChoice ::
  (ef `IsAtLeast` Traversable, ef []) =>
  Eff ef (Choice : es) a ->
  Eff ef es [a]
runChoice = interpretRaw (pure . pure) \cases
  Empty _ next ->
    case next $ Many isoSomeId implyAtLeast (pure []) pure of
      Many listIso travProof start go ->
        join <$> runChoice do
          inits <- start
          results <- traverse (poseChoice listIso travProof . go) inits
          pure $ join results
  Choose _ next ->
    case next $ Many isoSomeId implyAtLeast (pure [True, False]) pure of
      Many listIso travProof start go ->
        join <$> runChoice do
          inits <- start
          results <- traverse (poseChoice listIso travProof . go) inits
          pure $ join results

-- | Same as `runChoice`, but modifies a `Choice` that's not at the top of the
-- stack.
poseChoice ::
  Choice :> es =>
  [] `IsoSome` ef ->
  ef `Implies` Traversable ->
  Eff ef es a ->
  Eff ef es [a]
poseChoice (IsoSome (Iso lg gl)) imply =
  fmap gl . interposeRaw imply (lg . pure) \cases
    Empty _ next ->
      case next $ Many isoSomeId implyAtLeast (pure []) pure of
        many -> lg <$> runMany many
    Choose _ next ->
      case next $ Many isoSomeId implyAtLeast (pure [True, False]) pure of
        many -> lg <$> runMany many

-- | Executes all the threads
runMany :: Choice :> es => Many Choice (Eff ef es) a -> Eff ef es [a]
runMany (Many isoSomeId travProof start go) =
  join <$> poseChoice isoSomeId travProof do
    inits <- start
    results <- traverse (poseChoice isoSomeId travProof . go) inits
    pure $ join results

instance (Choice :> es, ef [], ef `IsAtLeast` Traversable) => Alternative (Eff ef es) where
  empty = send Empty
  a <|> b =
    send Choose >>= \case
      True -> a
      False -> b

-- | A provider for Choices. You can use this to scope the `Choice` threads.
data Collect :: Effect where
  Collect :: (ef `IsAtLeast` Traversable, ef []) => Eff ef (Choice : es) a -> Collect (Eff ef es) [a]

-- | Gathers all the threads of computation into a list.
collect :: (Collect :> es, ef []) => ef `IsAtLeast` Traversable => Eff ef (Choice : es) a -> Eff ef es [a]
collect action = send $ Collect action

-- | Provides the default `Choice` implementation.
runCollect :: ef Identity => Eff ef (Collect : es) a -> Eff ef es a
runCollect = interpret \_ (Collect action) -> pure $ runChoice action
