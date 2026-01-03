{-# LANGUAGE QuantifiedConstraints #-}

module Theseus.Effect.Error where

import Control.Monad (join)
import Control.Monad.Identity
import Data.Functor
import Theseus.Eff

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

runThrow :: ef (Either e) => Eff ef (Throw e : es) a -> Eff ef es (Either e a)
runThrow = interpretRaw (pure . pure) \(Throw e) _ next -> fmap takeFirstError $ runThrow $ finishThrown $ next $ Thrown e (pure ())

takeFirstError :: Either e e -> Either e a
takeFirstError (Left a) = Left a
takeFirstError (Right a) = Left a

runCatchNoRecovery :: (ef Maybe, forall w. Traversable w => ef w) => Eff Traversable (Catch : es) a -> Eff ef es (Maybe a)
runCatchNoRecovery = interpretRaw (pure . pure) \(Catch action _) _ continue -> do
  ran <- runCatchNoRecovery $ runMaybeCf $ continue $ MaybeCf $ either (const Nothing) Just <$> runThrow action
  pure $ join ran

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

instance ControlFlow MaybeCf Traversable where
  MaybeCf fmab `cfApply` fa = MaybeCf $ (\mab a -> fmap ($ a) mab) <$> fmab <*> fa
  MaybeCf fma `cfBind` afb = MaybeCf $ fma >>= traverse afb
  cfMap _ efToOut (MaybeCf fa) = MaybeCf $ efToOut fa
  cfRun _ handler (MaybeCf fa) = MaybeCf $ sequenceA <$> handler fa
