module Theseus.Effect.Reader where

import Control.Monad.Identity
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
-- All handlers must wrap their output in something. Wrapping in Identity will
-- be an extremely common case and should probably be hidden behind a helper
-- somewhere because users probably don't want to deal with unwrapping and
-- wrapping Identity all the time.
runReader r = fmap runIdentity . runReaderId r

runReaderId :: r -> Eff ef (Reader r : es) a -> Eff ef es (Identity a)
-- The first argument to handle says what we should do when no effects were
-- used. The `pure . pure` code just means that we want to do nothing
-- interesting.
runReaderId r = handle (pure . pure) (elabReader r)

elabReader :: r -> Handler (Reader r) ef es Identity
-- What's up with the recursive `runReaderId`? Handlers only run once and have
-- to be readded every time they run. This is cool for things like `State`
-- because they make `Put` really easy to implement. I think this is similar to
-- how control0 works as opposed to control.
elabReader r Ask next = runReaderId r $ next $ pure r
elabReader r (Local f m) next = runReaderId r $ next $ runIdentity <$> interposeLocal f m

interposeLocal :: Reader r `Member` es => (r -> r) -> Eff ef es a -> Eff ef es (Identity a)
interposeLocal @r f = interpose @(Reader r) (pure . pure) \eff next -> do
  x <- asks f
  interposeLocal f $
    case eff of
      Ask -> next $ pure x
      Local f' m -> next $ runIdentity <$> interposeLocal f' m

-- This is a version of Reader which completely ignores the function passed to
-- local. It's pointless and you should never use it, but it illustrates one of
-- the challenges with Coroutine.
runReaderNoLocal :: r -> Eff ef (Reader r : es) a -> Eff ef es a
runReaderNoLocal r = fmap runIdentity . runReaderNoLocalId r

runReaderNoLocalId :: r -> Eff ef (Reader r : es) a -> Eff ef es (Identity a)
runReaderNoLocalId r = handle (pure . pure) (elabReaderNoLocal r)

elabReaderNoLocal :: r -> Handler (Reader r) ef es Identity
elabReaderNoLocal r Ask next = runReaderNoLocalId r $ next $ pure r
elabReaderNoLocal r (Local _ m) next = runReaderNoLocalId r $ next m
