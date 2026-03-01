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
import Data.Functor
import Theseus.Constraints
import Theseus.Eff

-- # Choice

-- Choice is probably the most complicated effect in Theseus. It's first order,
-- but it requires complicated control flow and changes the output. Take a look
-- at Error first to understand the control flow operations.

-- | There's a lot to keep track of while handling `Choice`. The first
-- parameter tells us that all wrapping types will implement `Traversable`. The
-- second parameter tells us whether the part of the program we're running now
-- might contain more `Choice` operations. The third stores the current state
-- of all the threads in our program. The last represents the rest of the
-- program. We keep it separate so that we don't merge the threads together too
-- early.
data ManyItems lb ub es a where
  ManyItems ::
    lb `Implies` Traversable ->
    Maybe (Choice `IsMember` es) ->
    Eff lb ub es [a] ->
    (a -> Eff lb ub es b) ->
    ManyItems lb ub es b

deriving instance Functor (ManyItems lb ub es)

-- There's one of these functions for each of the "simple" constructors for
-- `CF`. Since the implementations are pretty noisy, keeping them separate
-- seemed best. That way we can focus on the complicated stuff later.

applyMany :: ManyItems lb ub es (a -> b) -> Eff lb ub es a -> ManyItems lb ub es b
applyMany (ManyItems lb member start go) ma = ManyItems lb member start \a -> go a <*> ma

bindMany :: ManyItems lb ub es a -> (a -> Eff lb ub es b) -> ManyItems lb ub es b
bindMany (ManyItems lb member start go) amb = ManyItems lb member start $ go >=> amb

raiseMany :: ManyItems lb ub es a -> ManyItems lb ub (e : es) a
raiseMany (ManyItems lb member start go) = ManyItems lb (fmap Deeper member) (raise start) (raise . go)

raiseManyUnder :: ManyItems lb ub (e : es) a -> ManyItems lb ub (e : newE : es) a
raiseManyUnder (ManyItems lb member start go) = ManyItems lb newMember (raiseUnder start) (raiseUnder . go)
 where
  newMember =
    member <&> \case
      (IsMember _) -> getProof
      (Deeper rest) -> Deeper $ Deeper rest

unrestrictMany ::
  lb `Implies` Traversable ->
  ubSend `Implies` lbSend ->
  ub `Implies` ubSend ->
  lbSend `Implies` lb ->
  ManyItems lbSend ubSend es a ->
  ManyItems lb ub es a
unrestrictMany isTrav bounded ub lb (ManyItems _ member start go) = ManyItems isTrav member (unrestrict' bounded ub lb start) (unrestrict' bounded ub lb . go)

runManyCf ::
  [] `IsoSome` ub ->
  lb `Implies` Traversable ->
  Maybe (Choice `IsMember` es) ->
  ManyItems lbSend ubSend esSend x ->
  CF (Eff lbSend ubSend esSend x) (Eff lb ub es) a ->
  ManyItems lb ub es a
runManyCf canUseList lbIsTrav member many = \case
  CfIn -> many
  CfFmap f cf -> f <$> runManyCf canUseList lbIsTrav member many cf
  CfApply cf ma -> applyMany (runManyCf canUseList lbIsTrav member many cf) ma
  CfBind cf amb -> bindMany (runManyCf canUseList lbIsTrav member many cf) amb
  CfRaise cf -> raiseMany $ runManyCf canUseList lbIsTrav (dig member) many cf
  CfRaiseUnder cf -> raiseManyUnder $ runManyCf canUseList lbIsTrav (digUnder member) many cf
  CfUnrestrict bounded ub lb cf -> unrestrictMany lbIsTrav bounded ub lb $ runManyCf (isoImplying canUseList ub) (transImply lb lbIsTrav) member many cf
  -- Most `Choice` implementations are depth first. They run one thread to
  -- completion, then they run the next. The problem with depth first is that
  -- it causes things like `State` to constantly go in and out of scope
  -- creating the "duplicate the world" semantics that are popular.
  --
  -- Theseus adopts a breadth first approach. We run all the threads in
  -- parallel. That means handlers aren't constantly going in and out of scope
  -- because all the threads will join before the interpreter goes out of
  -- scope.
  --
  -- What's up with the `newStart` variable? Basically we're doing manual
  -- type class resolution. We know the wrapper type implements `Traversable`,
  -- but GHC doesn't understand that. Instead we say that the wrapper type is
  -- isomorphic to something which does implement `Traversable`. We have to
  -- convert back and forth with that isomorphism to use the `sequenceA`
  -- function.
  CfRun handler cf -> case runManyCf canUseList lbIsTrav (fmap Deeper member) many cf of
    many@(ManyItems imply@(Implies go) member' _ _) -> ManyItems imply member newStart pure
     where
      newStart = go \(Iso lr rl) -> fmap (fmap rl . sequenceA . lr) $ handler $ runMany canUseList member' many
  -- Interpose is the exact same as run.
  CfInterpose handler cf -> case runManyCf canUseList lbIsTrav member many cf of
    many@(ManyItems imply@(Implies go) member' _ _) -> ManyItems imply member newStart pure
     where
      newStart = go \(Iso lr rl) -> fmap (fmap rl . sequenceA . lr) $ handler $ runMany canUseList member' many
  -- These next two functions are twisty so that the `CF` will always be used linearly.
  CfOnce implySend lifter handler cf -> case runManyCf canUseList lbIsTrav member many cf of
    many@(ManyItems travProof member' _ _) -> ManyItems travProof member newStart pure
     where
      implied = transImply implySend travProof
      newStart = do
        matchOn (sequenceA <$> runMany canUseList member' many) >>= \case
          Pure as ->
            case runManyCf canUseList lbIsTrav member (ManyItems (transImply implySend lbIsTrav) (member >>= lifter) as pure) handler of
              items -> runMany canUseList member items
          Impure eff lb ub lifter' next -> Eff \_ ->
            Impure eff lb ub lifter' $
              CfPutMeIn (\starts -> runMany canUseList member' $ runManyCf canUseList lbIsTrav member (ManyItems implied (member >>= lifter) starts pure) handler) next
  CfPutMeIn f cf -> case runManyCf canUseList lbIsTrav member many cf of
    many@(ManyItems travProof member _ _) -> ManyItems travProof member newStart pure
     where
      newStart = do
        matchOn (sequenceA <$> runMany canUseList member many) >>= \case
          -- TODO this is probably bad because I'm flattening the threads.
          -- I should create some tests to either show why this is fine or show
          -- why it's bad.
          Pure as -> fmap pure $ f $ fmap fold as
          Impure eff lb ub lifter next -> Eff \_ ->
            Impure eff lb ub lifter $
              fmap pure $
                CfPutMeIn f $
                  fmap fold <$> next

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
  Empty lb _ lifter next ->
    case runManyCf isoSomeId implyAtLeast (Just getProof) (ManyItems (transImply lb implyAtLeast) (lifter getProof) (pure []) pure) next of
      ManyItems travProof _ start go ->
        join <$> runChoice do
          inits <- start
          results <- traverse (poseChoice isoSomeId travProof . go) inits
          pure $ join results
  Choose lb _ lifter next ->
    case runManyCf isoSomeId implyAtLeast (Just getProof) (ManyItems (transImply lb implyAtLeast) (lifter getProof) (pure [True, False]) pure) next of
      ManyItems travProof _ start go ->
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
    Empty lb _ lifter next ->
      case runManyCf isoUb imply (Just getProof) (ManyItems (transImply lb imply) (lifter @Choice getProof) (pure []) pure) next of
        many -> lg <$> runMany isoUb (Just getProof) many
    Choose lb _ lifter next ->
      case runManyCf isoUb imply (Just getProof) (ManyItems (transImply lb imply) (lifter @Choice getProof) (pure [True, False]) pure) next of
        many -> lg <$> runMany isoUb (Just getProof) many

-- | Executes all the threads
runMany :: [] `IsoSome` ub -> Maybe (Choice `IsMember` es) -> ManyItems lb ub es a -> Eff lb ub es [a]
runMany listIso (Just proof) (ManyItems travProof _ start go) = withProof proof do
  join <$> poseChoice listIso travProof do
    inits <- poseChoice listIso travProof start
    results <- traverse (poseChoice listIso travProof . go) $ join inits
    pure $ join results
-- In this case we know that none of the computations will use `Choice`, so we
-- don't need to distribute.
runMany _ Nothing (ManyItems _ _ start go) = do
  inits <- start
  traverse go inits

instance Choice :> es => Alternative (Eff lb ub es) where
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
