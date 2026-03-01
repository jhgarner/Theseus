module Theseus.Effect.Error where

import Control.Applicative (Const (Const, getConst))
import Control.Monad (join)
import Control.Monad.Identity
import Data.Functor
import Data.Maybe (fromMaybe)
import Data.Monoid
import Theseus.Eff

-- # Error

-- Error is a good example of something with complicated control flow.

-- | We separate out the Throw and Catch effects so that you can easily scope
-- when throwing an exception is allowed.
newtype Throw e m a where
  Throw :: e -> Throw e m a

throw :: Throw e :> es => e -> Eff lb ub es a
throw e = send $ Throw e

-- | This is a provider for `Throw` effects. If you want to change what `Throw`
-- does, you can change the `Catch` interpreter.
data Catch m a where
  Catch :: lb (Either e) => Eff lb ub (Throw e : es) a -> (e -> Eff lb ub es a) -> Catch (Eff lb ub es) a

catch :: (Catch :> es, lb (Either e)) => Eff lb ub (Throw e : es) a -> (e -> Eff lb ub es a) -> Eff lb ub es a
catch action onThrow = send $ Catch action onThrow

runCatch :: lb Identity => Eff lb ub (Catch : es) a -> Eff lb ub es a
runCatch = interpret \_ (Catch action onThrow) ->
  pure $ runThrow action >>= either onThrow pure

runThrow :: forall e lb ub es a. lb (Either e) => Eff lb ub (Throw e : es) a -> Eff lb ub es (Either e a)
-- Although Throw is first order, it modifies the control flow, so we have to
-- use `interpretRaw`.
runThrow = interpretRaw isoSomeId (pure . pure) \(Throw e) _ _ _ next ->
  -- We consume the `next` function that was passed into our interpreter. Most
  -- other effect systems would simply ignore the continuation. Theseus doesn't
  -- ignore the continuation because we want finalizers to run.
  --
  -- Originally the `runThrow` function didn't have any of the finalizer stuff
  -- and Theseus didn't have the linearity constraints. After adding those,
  -- I had to add the `takeError` function call. That seemed weird, but really
  -- it's the same problem most languages with try-finally blocks have: what do
  -- you do when a finalizer throws an exception? Anyway, I think it's cool
  -- that the type system forces us to confront problems like this that are
  -- shared with non-functional non-statically typed languages. Since the
  -- problem is shared, the solutions can also be shared. Just like how Java
  -- added the `suppressed` field to its exception types so that the original
  -- exception wouldn't be lost, we could do something similar. For now we just
  -- ignore the original exception.
  fmap (takeError e) $ runThrow $ runEmptyCf (pure ()) next

takeError :: e -> Either e () -> Either e a
takeError _ (Left e) = Left e
takeError e (Right ()) = Left e

-- | Like `runCatch` except it completely ignores the catching block. If
-- anything throws, the entire computation finishes with `Nothing`.
runCatchNoRecovery :: (lb Maybe, lb `IsAtLeast` Traversable) => Eff lb ub (Catch : es) a -> Eff lb ub es (Maybe a)
runCatchNoRecovery = interpretRaw isoSomeId (pure . pure) \(Catch action _) _ _ _ next -> do
  ran <- runCatchNoRecovery $ runMaybeCf implyAtLeast (either (const Nothing) Just <$> runThrow action) next
  pure $ join ran

-- | This control flow represents a stopped computation. There are no active
-- threads, but we still have to track the finalizers.
runEmptyCf :: Eff lbSend ubSend esSend () -> CF (Eff lbSend ubSend esSend x) (Eff lb ub es) a -> Eff lb ub es ()
runEmptyCf go = \case
  CfIn -> go
  CfFmap _ cf -> runEmptyCf go cf
  CfApply cf _ -> runEmptyCf go cf
  CfBind cf _ -> runEmptyCf go cf
  CfOnce _ _ handler cf ->
    matchOn (runEmptyCf go cf) >>= \case
      Pure () -> runEmptyCf (pure ()) handler
      Impure eff lb ub lifter next -> Eff \_ ->
        Impure eff lb ub lifter $
          fmap getConst $
            CfPutMeIn (\ef -> Const <$> runEmptyCf (void ef) handler) $
              fmap (\() -> pure $ Const ()) next
  CfPutMeIn f cf -> do
    matchOn (runEmptyCf go cf) >>= \case
      Pure () -> void $ f $ pure mempty
      Impure eff lb ub lifter next -> Eff \_ ->
        Impure eff lb ub lifter $
          void $
            CfPutMeIn f $
              fmap (\() -> pure mempty) next
  CfUnrestrict bounded ub lb cf -> unrestrict' bounded ub lb $ runEmptyCf go cf
  CfRaise cf -> void $ raise $ runEmptyCf go cf
  CfRaiseUnder cf -> raiseUnder $ runEmptyCf go cf
  CfRun handler cf -> void $ handler $ runEmptyCf go cf
  CfInterpose handler cf -> void $ handler $ runEmptyCf go cf

-- This is an example of a control flow that uses Traversable. Why do Control
-- Flows ever need `Traversable` or really anything more strict than
-- `Anything`? The interpreter's scope is separate from the sender's scope.
-- Getting information from the interpreter to the sender is easy, but passing
-- information in the opposite direction is harder. You can only get
-- information out of the sender and into the interpreter by running the
-- continuation, which means running all the other effects that were added to
-- the stack after the current interpreter. Some of those other interpreters
-- might want to change the type of the return value. Now we have a problem.
-- Our current interpreter wants to thread some information through the
-- continuation's output, but the continuation might wrap the output in
-- arbitrary other things. The `Traversable` constraint ensures that we can
-- extract the extra information from the wrapped output.
--
-- A `Traversable` constraint isn't the only way to handle this. If the
-- information we wanted to pass around were `Distributive`, we would only need
-- `Functor`. We could also go stricter and require that our threaded
-- information be never duplicated or lost by requiring some kind of
-- `LinearTraversable` or `AffineTraversable`. The former would would remove
-- the `Applicative` constraint from the `traverse` function, and the latter
-- would only require a `Pure` typeclass. There's also probably something fun
-- to do with `Comonad` to say that it's OK to duplicate or drop the wrapper.
-- That also seems to be related to linearity. We could argue that
-- `data StateOutput s a = SO s a` is not a `Comonad` because duplicating or
-- dropping the state leads to strange semantics. That would prevent certain
-- effect orderings at compile time. We could have an `UnliftIO` effect which
-- requires `Comonad` which would conveniently line up with the usual UnliftIO
-- restrictions. Anyway, at this point I'm probably confusing things, but
-- I think it's an interesting direction to study.
runMaybeCf ::
  lb `Implies` Traversable ->
  Eff lbSend ubSend esSend (Maybe x) ->
  CF (Eff lbSend ubSend esSend x) (Eff lb ub es) a ->
  Eff lb ub es (Maybe a)
runMaybeCf lbIsTrav go = \case
  CfIn -> go
  CfFmap f cf -> fmap f <$> runMaybeCf lbIsTrav go cf
  CfApply cfab ma -> (\mab a -> fmap ($ a) mab) <$> runMaybeCf lbIsTrav go cfab <*> ma
  CfBind cfa amb -> runMaybeCf lbIsTrav go cfa >>= traverse amb
  CfOnce _ _ handler cf ->
    matchOn (runMaybeCf lbIsTrav go cf) >>= \case
      Pure (Just a) -> Just <$> runLinearCf a handler
      Pure Nothing -> ($> Nothing) $ runEmptyCf (pure ()) handler
      Impure eff lb' ub lifter next -> Eff \_ ->
        Impure eff lb' ub lifter $
          -- TODO This is weird because it acts as a funnel converting all the
          -- other threads of computation into a single one. That's probably
          -- going to be confusing. Maybe everything should be lists?
          fmap getFirst $
            CfPutMeIn (\ef -> First <$> runMaybeCf lbIsTrav (fmap getFirst ef) handler) $
              sequenceA . First <$> next
  CfPutMeIn f cf ->
    matchOn (runMaybeCf lbIsTrav go cf) >>= \case
      Pure (Just a) -> Just <$> f a
      -- TODO Wow this is also weird. By adding the `Just` in all cases,
      -- we're saying that the MaybeCf will defer all control flow questions
      -- to the other cf. Using lists for everything might be cool, but I'm
      -- struggling to wrap my head around distributing vs not distributing
      -- effects.
      Pure Nothing -> Just <$> f (pure mempty)
      Impure eff lb ub lifter next -> Eff \_ ->
        Impure eff lb ub lifter $
          fmap Just $
            CfPutMeIn f $
              fromMaybe (pure mempty) <$> next
  CfUnrestrict bounded ub lb cf -> unrestrict' bounded ub lb $ runMaybeCf (transImply lb lbIsTrav) go cf
  CfRaise cf -> raise $ runMaybeCf lbIsTrav go cf
  CfRaiseUnder cf -> raiseUnder $ runMaybeCf lbIsTrav go cf
  CfRun handler cf -> lbIsTrav `impliesThat` \(Iso lr rl) -> fmap rl . sequenceA . lr <$> handler (runMaybeCf lbIsTrav go cf)
  CfInterpose handler cf -> lbIsTrav `impliesThat` \(Iso lr rl) -> fmap rl . sequenceA . lr <$> handler (runMaybeCf lbIsTrav go cf)
