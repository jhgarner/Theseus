{-# LANGUAGE QuantifiedConstraints #-}

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

-- | We separate out the Throw and Catch effects so that you can more easily
-- scope when throwing an exception is allowed.
newtype Throw e m a where
  Throw :: e -> Throw e m a

throw :: Throw e :> es => e -> Eff lb ub es a
throw e = send $ Throw e

-- | This is a provider for `Throw` effects.
data Catch m a where
  Catch :: lb (Either e) => Eff lb ub (Throw e : es) a -> (e -> Eff lb ub es a) -> Catch (Eff lb ub es) a

catch :: (Catch :> es, lb (Either e)) => Eff lb ub (Throw e : es) a -> (e -> Eff lb ub es a) -> Eff lb ub es a
catch action onThrow = send $ Catch action onThrow

runCatch :: lb Identity => Eff lb ub (Catch : es) a -> Eff lb ub es a
runCatch = interpret \_ (Catch action onThrow) ->
  pure $ runThrow action >>= either onThrow pure

-- | A control flow data type which ignores any attempts to continue the
-- control flow. Instead it keeps track of the value that was thrown and
-- a series of finalizers to run.
data Thrown e eff f a = Thrown {getThrown :: e, finalizers :: f ()}
  deriving (Functor)

finishThrown :: Functor f => Thrown e eff f a -> f e
finishThrown (Thrown e finalizers) = finalizers $> e

instance ControlFlow (Thrown e) Anything where
  -- Note how it ignores the rhs of these operations. It acts a lot like Const.
  Thrown e f `cfApply` _ = Thrown e f
  Thrown e f `cfBind` _ = Thrown e f
  cfMap _ _ handler (Thrown e f) = Thrown e $ handler f
  cfOnce @_ @_ @eff _ member' handler (Thrown e f) = Thrown e do
    matchOn f >>= \case
      Pure () -> runNothingCf $ handler implying member' $ NothingCf $ pure ()
      Impure eff lb ub lifter next -> Eff \_ -> Impure eff lb ub lifter \imply member x ->
        fmap getConst $ cfPutMeIn member (fmap Const . runNothingCf . handler implying member' . NothingCf @eff . void) $ (\() -> pure $ Const ()) <$> next imply member x
  cfPutMeIn _ f (Thrown e fin) = Thrown e do
    matchOn fin >>= \case
      Pure a -> void $ f $ pure a $> mempty
      Impure eff lb ub lifter next -> Eff \_ -> Impure eff lb ub lifter \imply member x ->
        void $ cfPutMeIn member f $ (\() -> pure mempty) <$> next imply member x

  -- Note that we don't ignore the handler. This is because `cfRun` requires
  -- that the `handler` parameter be used linearly.
  cfRun _ handler (Thrown e f) = Thrown e $ handler f $> ()

runThrow :: forall e lb ub es a. lb (Either e) => Eff lb ub (Throw e : es) a -> Eff lb ub es (Either e a)
-- Although Throw is first order, it modifies the control flow, so we have to
-- use `interpretRaw`.
runThrow = interpretRaw isoSomeId (pure . pure) \(Throw e) _ _ _ next ->
  -- We run the `next` function that was passed into our interpreter. Most
  -- other effect systems would simply ignore the continuation. Theseus doesn't
  -- ignore the continuation because we want finalizers to run.
  --
  -- Originally the `runThrow` function didn't have any of the finalizer stuff
  -- and Theseus didn't have the linearity constraints. After adding those,
  -- I had to add the `takeError` function call. That seemed weird, but really
  -- it's the same problem most languages with try-finally blocks have: what do
  -- you do when the finalizer throws an exception? Anyway, I think it's cool
  -- that the type system forces us to confront problems like this that are
  -- shared with non-functional non-statically typed languages. Since the
  -- solutions are shared, the solutions can also be shared. Just like how Java
  -- added the `suppressed` field to its exception types so that the original
  -- exception wouldn't be lost, we could do something similar. For now we just
  -- ignore the original exception.
  fmap takeError $ runThrow $ finishThrown $ next implying (Just $ getProof @(Throw e)) $ Thrown e (pure ())

takeError :: Either e e -> Either e a
takeError = either Left Left

-- | Like `runCatch` except it completely ignores the catching block. If
-- anything throws, the entire computation finishes with `Nothing`.
runCatchNoRecovery :: (lb Maybe, lb `IsAtLeast` Traversable) => Eff lb ub (Catch : es) a -> Eff lb ub es (Maybe a)
runCatchNoRecovery = interpretRaw isoSomeId (pure . pure) \(Catch action _) lb _ _ next -> do
  ran <- runCatchNoRecovery $ runMaybeCf $ next implyAtLeast (Just $ getProof @Catch) $ MaybeCf (transImply lb implyAtLeast) $ either (const Nothing) Just <$> runThrow action
  pure $ join ran

data MaybeCf eff f a where
  MaybeCf ::
    {imply :: lb `Implies` Traversable, runMaybeCf :: Eff lb ub es (Maybe a)} ->
    MaybeCf eff (Eff lb ub es) a
deriving instance Functor (MaybeCf eff f)

newtype NothingCf eff f a = NothingCf {runNothingCf :: f ()}
  deriving (Functor)

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
instance ControlFlow MaybeCf Traversable where
  MaybeCf imply fmab `cfApply` fa = MaybeCf imply $ (\mab a -> fmap ($ a) mab) <$> fmab <*> fa
  MaybeCf imply fma `cfBind` afb = MaybeCf imply $ fma >>= traverse afb
  cfOnce @_ @_ @eff lb' member' handler (MaybeCf imply' f) = MaybeCf imply' do
    matchOn f >>= \case
      Pure (Just a) -> fmap Just $ runIdentityCf $ handler implying member' $ IdentityCf a
      Pure Nothing -> ($> Nothing) $ runNothingCf $ handler implying member' $ NothingCf $ pure ()
      Impure eff lb ub lifter next -> Eff \_ -> Impure eff lb ub lifter \imply member x ->
        -- TODO This is weird because it acts as a funnel converting all the
        -- other threads of computation into a single one. That's probably
        -- going to be confusing. Maybe everything should be lists?
        fmap getFirst $ cfPutMeIn member (fmap First . runMaybeCf . handler @_ @eff imply' member' . MaybeCf (transImply lb' imply') . fmap getFirst) $ sequenceA . First <$> next imply member x
  cfPutMeIn _ f (MaybeCf imply' fin) = MaybeCf imply' do
    matchOn fin >>= \case
      Pure (Just a) -> Just <$> f a
      -- TODO Wow this is also weird. By adding the `Just` in all cases,
      -- we're saying that the MaybeCf will defer all control flow questions
      -- to the other cf. Using lists for everything might be cool, but I'm
      -- struggling to wrap my head around distributing vs not distributing
      -- effects.
      Pure Nothing -> Just <$> f (pure mempty)
      Impure eff lb ub lifter next -> Eff \_ -> Impure eff lb ub lifter \imply member x ->
        fmap Just $ cfPutMeIn member f $ fromMaybe (pure mempty) <$> next imply member x
  cfMap _ lb efToOut (MaybeCf _ fa) = MaybeCf lb $ efToOut fa
  cfRun _ handler (MaybeCf (Implies imply) fa) = imply \(Iso lr rl) -> MaybeCf (Implies imply) $ fmap rl . sequenceA . lr <$> handler fa

instance ControlFlow NothingCf Anything where
  NothingCf fmab `cfApply` _ = NothingCf fmab
  NothingCf fma `cfBind` _ = NothingCf fma
  cfOnce @_ @_ @eff _ member' handler (NothingCf f) = NothingCf do
    matchOn f >>= \case
      Pure () -> runNothingCf $ handler implying member' $ NothingCf $ pure ()
      Impure eff lb ub lifter next -> Eff \_ -> Impure eff lb ub lifter \imply member x ->
        fmap getConst $ cfPutMeIn member (fmap Const . runNothingCf . handler implying member' . NothingCf @eff . void) $ (\() -> pure $ Const ()) <$> next imply member x
  cfPutMeIn _ f (NothingCf fin) = NothingCf do
    matchOn fin >>= \case
      Pure a -> void $ f $ pure a $> mempty
      Impure eff lb ub lifter next -> Eff \_ -> Impure eff lb ub lifter \imply member x ->
        void $ cfPutMeIn member f $ (\() -> pure mempty) <$> next imply member x
  cfMap _ _ efToOut (NothingCf fin) = NothingCf $ efToOut fin
  cfRun _ handler (NothingCf fin) = NothingCf $ void $ handler fin

newtype ComposeCfs eff cf f a = Composed {runComposed :: f ()}
  deriving (Functor)
