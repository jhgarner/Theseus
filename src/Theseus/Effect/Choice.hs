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
-- at Error first to understand the control flow operations. Also take a look
-- at EffType to understand how Theseus works behind the scenes.

-- | This is the `ControlFlow` that `Choice` will use. There's the `Thrown`
-- control flow that handles 0 threads of computation, `IdentityCf` that
-- handles 1, and `MaybeCf` that handles 0 or 1. `Many` handles 0 or more
-- threads of computation.
data Many eff m a where
  Many ::
    -- This `ef` constraint is here because we're going to `runChoice` in the
    -- middle of the control flow. That's weird, but it's what allows us to use
    -- the other `handler`s linearly
    ef [] =>
    -- We need to keep track of this because we're going to use `interpose` to
    -- change how `Choice` is run while running the continuation.
    ef `Implies` Traversable ->
    -- These are the current values across all our threads of computation.
    Eff ef es [a] ->
    -- This is the operation we'd like to apply to each value.
    (a -> Eff ef es b) ->
    Many Choice (Eff ef es) b

deriving instance Functor (Many eff m)

instance ControlFlow Many Traversable where
  Many travProof start go `cfApply` fa = Many travProof start ((<*> fa) . go)
  Many travProof start go `cfBind` afb = Many travProof start (go >=> afb)
  cfMap implication handler (Many _ start go) = Many implication (handler start) (handler . go)

  -- Most `Choice` implementations are depth first. They run on thread to
  -- completion, then they run the other. The problem with depth first is that
  -- it causes things like `State` to constantly go in and out of scope
  -- creating the "duplicate the world" semantics that are popular.
  --
  -- Theseus adopts a breadth first approach. We run all the threads in
  -- parallel. That means handlers aren't constantly going in and out of scope
  -- because all the threads will complete at the same time.
  cfRun implication handler many@Many{} = Many implication newStart pure
   where
    -- We require `Traversable` because we need to know how many threads are in
    -- the output.
    newStart = fmap sequenceA $ handler $ runMany many

-- There we go! That's how Theseus handles nondeterminism while avoiding the
-- handler ordering problems.

-- | Represents Nondeterminism kind of like what ListT does. You should use the
-- `Alternative` operations to send `Choice` effects.
data Choice :: Effect where
  Empty :: Choice (Eff Traversable es) a
  Choose :: Choice (Eff Traversable es) Bool

-- | Runs a choice that causes all other effects to act globally over all the
-- threads.
runChoice ::
  (forall w. Traversable w => ef w) =>
  Eff Traversable (Choice : es) a ->
  Eff ef es [a]
runChoice = interpretRaw (pure . pure) \cases
  Empty _ next ->
    case next $ Many implying (pure []) pure of
      Many travProof start go ->
        join <$> runChoice do
          inits <- start
          results <- traverse (poseChoice travProof . go) inits
          pure $ join results
  Choose _ next ->
    case next $ Many implying (pure [True, False]) pure of
      Many travProof start go ->
        join <$> runChoice do
          inits <- start
          results <- traverse (poseChoice travProof . go) inits
          pure $ join results

-- | Same as `runChoice`, but modifies a `Choice` that's not at the top of the
-- stack.
poseChoice ::
  (ef [], Choice `Member` es) =>
  ef `Implies` Traversable ->
  Eff ef es a ->
  Eff ef es [a]
poseChoice (Implies traversable) = interposeRaw pure \cases
  Empty _ next ->
    case traversable $ next $ Many implying (pure []) pure of
      many -> runMany many
  Choose _ next ->
    case traversable $ next $ Many implying (pure [True, False]) pure of
      many -> runMany many

-- | Executes all the threads
runMany :: Choice `Member` es => Many Choice (Eff ef es) a -> Eff ef es [a]
runMany (Many travProof start go) =
  join <$> poseChoice travProof do
    inits <- start
    results <- traverse (poseChoice travProof . go) inits
    pure $ join results

instance Choice `Member` es => Alternative (Eff Traversable es) where
  empty = send Empty
  a <|> b =
    send Choose >>= \case
      True -> a
      False -> b

-- | A provider for Choices. You can use this to scope the `Choice` threads.
data Collect :: Effect where
  Collect :: (forall w. Traversable w => ef w) => Eff Traversable (Choice : es) a -> Collect (Eff ef es) [a]

-- | Gathers all the threads of computation into a list.
collect :: Collect `Member` es => (forall w. Traversable w => ef w) => Eff Traversable (Choice : es) a -> Eff ef es [a]
collect action = send $ Collect action

-- | Provides the default `Choice` implementation.
runCollect :: ef Identity => Eff ef (Collect : es) a -> Eff ef es a
runCollect = interpret \_ (Collect action) -> pure $ runChoice action
