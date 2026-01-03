module Theseus.Effect.Reader where

import Control.Monad.Identity (Identity)
import Theseus.Eff

data Reader r m a where
  Ask :: Reader r m r
  Local :: ef Identity => (r -> r) -> Eff ef es a -> Reader r (Eff ef es) a

ask :: Reader r `Member` es => Eff ef es r
ask = send Ask

local :: ef Identity => Reader r `Member` es => (r -> r) -> Eff ef es a -> Eff ef es a
local f action = send $ Local f action

asks :: Reader r `Member` es => (r -> a) -> Eff ef es a
asks f = fmap f ask

runReader :: forall r ef es a. ef Identity => r -> Eff ef (Reader r : es) a -> Eff ef es a
runReader r = interpret \sender -> \case
  Ask -> pure $ pure r
  Local f m -> pure $ sender @(Reader r) $ interposeLocal f m

interposeLocal :: (Reader r `Member` es, ef Identity) => (r -> r) -> Eff ef es a -> Eff ef es a
interposeLocal @r f = interpose @(Reader r) \cases
  Ask _ next -> do
    x <- asks f
    next $ pure x
  (Local f' m) sender next -> next $ sender @(Reader r) $ interposeLocal f' m

-- This is a version of Reader which completely ignores the function passed to
-- local. It's pointless and you should never use it, but it illustrates one of
-- the challenges with Coroutine.He's
runReaderNoLocal :: ef Identity => r -> Eff ef (Reader r : es) a -> Eff ef es a
runReaderNoLocal r = interpret \_ -> \case
  Ask -> pure $ pure r
  Local _ m -> pure m
