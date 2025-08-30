module Theseus.Effect.Reader where

import Theseus.Eff

data Reader r m a where
  Ask :: Reader r m r
  Local :: (r -> r) -> Eff ef es a -> Reader r (Eff ef es) a

ask :: Reader r `Member` es => Eff ef es r
ask = send Ask

local :: Reader r `Member` es => (r -> r) -> Eff ef es a -> Eff ef es a
local f action = send $ Local f action

asks :: Reader r `Member` es => (r -> a) -> Eff ef es a
asks f = fmap f ask

runReader :: r -> Eff ef (Reader r : es) a -> Eff ef es a
runReader r = handle \cases
  Ask continue -> continue $ pure r
  (Local f m) continue -> continue $ interposeLocal f m

interposeLocal :: Reader r `Member` es => (r -> r) -> Eff ef es a -> Eff ef es a
interposeLocal @r f = interpose @(Reader r) \cases
  Ask next -> do
    x <- asks f
    next $ pure x
  (Local f' m) next -> next $ interposeLocal f' m

-- This is a version of Reader which completely ignores the function passed to
-- local. It's pointless and you should never use it, but it illustrates one of
-- the challenges with Coroutine.
runReaderNoLocal :: r -> Eff ef (Reader r : es) a -> Eff ef es a
runReaderNoLocal r = handle \cases
  Ask next -> next $ pure r
  (Local _ m) continue -> continue m
