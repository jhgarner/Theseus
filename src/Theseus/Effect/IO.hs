{-# OPTIONS_GHC -Wno-orphans #-}

module Theseus.Effect.IO where

import Control.Monad.IO.Class
import Theseus.Eff

data EIO m a where
  LiftIO :: IO a -> EIO m a

runEffIO :: Eff Boring '[EIO] a -> IO a
runEffIO =
  runEff . handleRaw (pure . pure) \(LiftIO ioa) _ continue ->
    pure $ runEffIO =<< getComposeCf (continue $ ComposeCf $ fmap pure ioa)

instance EIO `Member` es => MonadIO (Eff ef es) where
  liftIO = send . LiftIO

newtype ComposeCf f eff g a = ComposeCf {getComposeCf :: f (g a)}
  deriving (Functor)

instance Functor m => ControlFlow (ComposeCf m) Boring where
  ComposeCf mfab `cfApply` fa = ComposeCf $ fmap (<*> fa) mfab
  ComposeCf mfa `cfBind` afb = ComposeCf $ fmap (>>= afb) mfa
  cfMap _ handler (ComposeCf mfa) = ComposeCf $ fmap handler mfa
  cfRun _ handler (ComposeCf mfa) = ComposeCf $ fmap handler mfa
