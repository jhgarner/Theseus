{-# LANGUAGE QuantifiedConstraints #-}

module Theseus.Effect.Error where

import Control.Monad (join)
import Control.Monad.Identity
import Data.Functor
import Debug.Trace
import Theseus.Eff
import Theseus.Interpreters (IdentityCf (IdentityCf, runIdentityCf))

-- # Error

-- Error is a good example of something with complicated control flow.

-- | We separate out the Throw and Catch effects so that you can more easily
-- scope when throwing an exception is allowed.
newtype Throw e m a where
  Throw :: e -> Throw e m a

throw :: Throw e `Member` es => e -> Eff ef es a
throw = send . Throw

data Catch m a where
  Catch :: ef (Either e) => Eff ef (Throw e : es) a -> (e -> Eff ef es a) -> Catch (Eff ef es) a

catch :: (Catch `Member` es, ef (Either e)) => Eff ef (Throw e : es) a -> (e -> Eff ef es a) -> Eff ef es a
catch action onThrow = send $ Catch action onThrow

runCatch :: ef Identity => Eff ef (Catch : es) a -> Eff ef es a
runCatch = interpret \_ (Catch action onThrow) ->
  pure $ runThrow action >>= either onThrow pure

runThrow :: forall e ef es a. ef (Either e) => Eff ef (Throw e : es) a -> Eff ef es (Either e a)
-- Although Throw is first order, it modifies the control flow, so we have to
-- use `interpretRaw`. Note though that we still run the `next` function that
-- was passed into our interpreter. Most other effect systems would simply
-- ignore the continuation. Theseus doesn't ignore the continuation because we
-- want finalizers to run.
runThrow = interpretRaw (pure . pure) \(Throw e) _ next ->
  fmap takeError $ runThrow $ finishThrown $ next $ Thrown e (pure ())

takeError :: Either e e -> Either e a
takeError = either Left Left

-- | Like `runCatch` except it completely ignores the catching block. If
-- anything throws, the entire computation finishes with `Nothing`.
runCatchNoRecovery :: (ef Identity, ef (Either ())) => Eff ef (Catch : es) a -> Eff ef es (Maybe a)
runCatchNoRecovery = using (fmap eitherToMaybe . runThrow @()) $ interpret \sender (Catch action _) -> do
  pure do
    traceShowM "Trying to do the thing"
    thrown <- runThrow action
    traceShowM "Again Trying"
    case thrown of
      Left _ -> sender @(Throw ()) throw ()
      Right a -> pure a

eitherToMaybe :: Either () a -> Maybe a
eitherToMaybe (Left ()) = Nothing
eitherToMaybe (Right a) = Just a

data Thrown e eff f a = Thrown {getThrown :: e, finalizers :: f ()}
  deriving (Functor)

finishThrown :: Functor f => Thrown e eff f a -> f e
finishThrown (Thrown e finalizers) = finalizers $> e

instance ControlFlow (Thrown e) Anything where
  Thrown e f `cfApply` _ = Thrown e f
  Thrown e f `cfBind` _ = Thrown e f
  cfMap _ handler (Thrown e f) = Thrown e $ handler f
  cfRun _ handler (Thrown e f) = Thrown e $ handler f $> ()

newtype MaybeCf eff f a = MaybeCf {runMaybeCf :: f (Maybe a)}
  deriving (Functor)

-- This is an example of a control flow that uses Traversable. It requires
-- Traversable because we need to keep track of whether something was thrown.
-- Imagine something like the following:
-- ```
-- runCatchNoRecovery do
--  catch (pure ()) pure
--  runCoroutine yield
-- ```
-- after `Catch` is sent, the interpreter attempts to continue running and wants to detect whether or not  `runCatchNoRecovery` has no idea whether the
instance ControlFlow MaybeCf Traversable where
  MaybeCf fmab `cfApply` fa = MaybeCf $ (\mab a -> fmap ($ a) mab) <$> fmab <*> fa
  MaybeCf fma `cfBind` afb = MaybeCf $ fma >>= traverse afb
  cfMap _ efToOut (MaybeCf fa) = MaybeCf $ efToOut fa
  cfRun _ handler (MaybeCf fa) = MaybeCf $ sequenceA <$> handler fa
