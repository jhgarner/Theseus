{-# OPTIONS_GHC -Wno-orphans #-}

module Theseus.Effect.IO where

import Control.Monad.IO.Class
import Theseus.ControlFlow
import Theseus.Eff

data EIO m a where
  LiftIO :: IO a -> EIO m a

runEffIO :: Eff Boring '[EIO] a -> IO a
runEffIO =
  runEff . handleRaw (pure . pure) \(LiftIO ioa) continue ->
    pure $ runEffIO =<< getComposeCf (continue $ ComposeCf $ fmap pure ioa)

instance EIO `Member` es => MonadIO (Eff ef es) where
  liftIO = send . LiftIO

-- TODO is UnliftIO possible? You might be able to use `Const` as the threaded
-- state to sneak the IO values out of `next`. Then you can call `next` for
-- real? I might actually be bad if that works?
