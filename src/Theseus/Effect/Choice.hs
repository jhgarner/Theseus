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
import Data.Foldable
import Theseus.Constraints
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
    {unMany :: [] `IsoSome` ub -> ManyItems lb ub es a} ->
    Many Choice (Eff lb ub es) a

manyUn :: IsoSome [] ub -> Many Choice (Eff lb ub es) a -> ManyItems lb ub es a
manyUn = flip unMany

data ManyItems lb ub es a where
  ManyItems ::
    lb `Implies` Traversable ->
    -- These are the current values across all our threads of computation.
    Eff lb ub es [a] ->
    -- This is the operation we'd like to run on each thread.
    (a -> Eff lb ub es b) ->
    ManyItems lb ub es b
deriving instance Functor (ManyItems lb ub es)

deriving instance Functor (Many eff m)

instance ControlFlow Many Traversable where
  Many act `cfApply` fa = Many \listIso -> case act listIso of
    ManyItems travProof start go -> ManyItems travProof start ((<*> fa) . go)
  Many act `cfBind` afb = Many \listIso -> case act listIso of
    ManyItems travProof start go -> ManyItems travProof start (go >=> afb)
  cfMap ub isTrav handler (Many act) = Many \listIso -> case act (isoImplying listIso ub) of
    ManyItems _ start go -> ManyItems isTrav (handler start) (handler . go)
  cfOnce @_ @_ @eff implySend member' handler (Many act) = Many \listIso -> case act listIso of
    many@(ManyItems travProof _ _) -> ManyItems travProof newStart pure
     where
      implied = transImply implySend travProof
      newStart = do
        matchOn (sequenceA <$> runMany listIso member' many) >>= \case
          Pure as ->
            case handler travProof member' $ Many $ const $ ManyItems (transImply implySend travProof) as pure of
              Many act -> runMany listIso member' $ act listIso
          Impure eff lb ub lifter next -> Eff \_ -> Impure eff lb ub lifter \imply member x ->
            cfPutMeIn member (\starts -> runMany listIso member' $ manyUn listIso $ handler @_ @eff travProof member' $ Many \_ -> ManyItems implied starts pure) $ next imply member x
  cfPutMeIn member f (Many act) = Many \listIso -> case act listIso of
    many@(ManyItems travProof _ _) -> ManyItems travProof newStart pure
     where
      newStart = do
        matchOn (sequenceA <$> runMany listIso member many) >>= \case
          -- TODO this is probably bad because I'm flattening the threads.
          -- I should create some tests to either show why this is fine or show
          -- why it's bad.
          Pure as -> fmap pure $ f $ fmap fold as
          Impure eff lb ub lifter next -> Eff \_ -> Impure eff lb ub lifter \imply member x ->
            fmap pure $ cfPutMeIn member f $ fmap fold <$> next imply member x

  -- Most `Choice` implementations are depth first. They run one thread to
  -- completion, then they run the next. The problem with depth first is that
  -- it causes things like `State` to constantly go in and out of scope
  -- creating the "duplicate the world" semantics that are popular.
  --
  -- Theseus adopts a breadth first approach. We run all the threads in
  -- parallel. That means handlers aren't constantly going in and out of scope
  -- because all the threads will join before the interpreter goes out of
  -- scope.
  cfRun member handler (Many act) = Many \listIso -> case act listIso of
    many@(ManyItems imply@(Implies go) _ _) -> ManyItems imply newStart pure
     where
      -- We require `Traversable` because we need to know how many threads made
      -- it past the other interpreter.
      newStart = go \(Iso lr rl) -> fmap (fmap rl . sequenceA . lr) $ handler $ runMany listIso member many

-- There we go! That's how Theseus handles nondeterminism while avoiding the
-- handler ordering problems.

-- | Represents Nondeterminism kind of like what ListT does. You should use the
-- `Alternative` operations to send `Choice` effects.
data Choice :: Effect where
  -- Do these constraints leak unfortunate implementation details? Yes. I don't
  -- know how to get rid of them though.
  Empty :: Choice (Eff lb ub es) a
  Choose :: Choice (Eff lb ub es) Bool

-- | Runs a choice that causes all other effects to act globally over all the
-- threads.
runChoice ::
  (lb `IsAtLeast` Traversable, ub []) =>
  Eff lb ub (Choice : es) a ->
  Eff lb ub es [a]
runChoice act = Eff \facts@Facts{bounded} -> effUn facts $ with act $ interpretRaw (isoImplying isoSomeId bounded) (pure . pure) \cases
  Empty lb _ _ next ->
    case manyUn isoSomeId $ next implyAtLeast (Just getProof) $ Many \_ -> ManyItems (transImply lb implyAtLeast) (pure []) pure of
      ManyItems travProof start go ->
        join <$> runChoice do
          inits <- start
          results <- traverse (poseChoice isoSomeId travProof . go) inits
          pure $ join results
  Choose lb _ _ next ->
    case manyUn isoSomeId $ next implyAtLeast (Just getProof) $ Many \_ -> ManyItems (transImply lb implyAtLeast) (pure [True, False]) pure of
      ManyItems travProof start go ->
        join <$> runChoice do
          inits <- start
          results <- traverse (poseChoice isoSomeId travProof . go) inits
          pure $ join results

-- | Same as `runChoice`, but modifies a `Choice` that's not at the top of the
-- stack.
poseChoice ::
  Choice :> es =>
  [] `IsoSome` ub ->
  lb `Implies` Traversable ->
  Eff lb ub es a ->
  Eff lb ub es [a]
poseChoice isoUb imply action = do
  Facts{bounded} <- getFacts
  IsoSome (Iso lg gl) <- pure $ isoImplying isoUb bounded
  fmap gl $ with action $ interposeRaw imply (lg . pure) \cases
    Empty lb _ _ next ->
      case manyUn isoUb $ next $ Many \_ -> ManyItems (transImply lb imply) (pure []) pure of
        many -> lg <$> runMany isoUb (Just getProof) many
    Choose lb _ _ next ->
      case manyUn isoUb $ next $ Many \_ -> ManyItems (transImply lb imply) (pure [True, False]) pure of
        many -> lg <$> runMany isoUb (Just getProof) many

-- | Executes all the threads
runMany :: [] `IsoSome` ub -> Maybe (Choice `IsMember` es) -> ManyItems lb ub es a -> Eff lb ub es [a]
runMany listIso (Just proof) (ManyItems travProof start go) = withProof proof do
  join <$> poseChoice listIso travProof do
    inits <- start
    results <- traverse (poseChoice listIso travProof . go) inits
    pure $ join results
-- In this case we know that none of the computations will use `Choice`, so we
-- don't need to distribute.
runMany _ Nothing (ManyItems _ start go) = do
  inits <- start
  traverse go inits

instance (Choice :> es, lb [], lb `IsAtLeast` Traversable) => Alternative (Eff lb ub es) where
  empty = send Empty
  a <|> b =
    send Choose >>= \case
      True -> a
      False -> b

-- | A provider for Choices. You can use this to scope the `Choice` threads.
data Collect :: Effect where
  Collect :: (lb `IsAtLeast` Traversable, ub []) => Eff lb ub (Choice : es) a -> Collect (Eff lb ub es) [a]

-- | Gathers all the threads of computation into a list.
collect :: (Collect :> es, ub [], lb `IsAtLeast` Traversable) => Eff lb ub (Choice : es) a -> Eff lb ub es [a]
collect action = send $ Collect action

-- | Provides the default `Choice` implementation.
runCollect :: lb Identity => Eff lb ub (Collect : es) a -> Eff lb ub es a
runCollect = interpret \_ (Collect action) -> pure $ runChoice action
