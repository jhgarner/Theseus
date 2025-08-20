{-# OPTIONS_GHC -Wno-orphans #-}

module Theseus.Effect.IO where

import Control.Monad.IO.Class
import Control.Monad.Identity
import Theseus.Eff
import Theseus.Union

data EIO m a where
  LiftIO :: IO a -> EIO m a

runEffIO :: Eff Boring '[EIO] a -> IO a
runEffIO (Eff (Pure a)) = pure a
runEffIO (Eff (Impure (This (LiftIO io)) next)) = io >>= runEffIO . fmap runIdentity . next . pure . pure
runEffIO (Eff (Impure (That union) _)) = case union of {}

instance EIO `Member` es => MonadIO (Eff ef es) where
  liftIO = send . LiftIO

-- TODO is UnliftIO possible? You might be able to use `Const` as the threaded
-- state to sneak the IO values out of `next`. Then you can call `next` for
-- real? I might actually be bad if that works?
