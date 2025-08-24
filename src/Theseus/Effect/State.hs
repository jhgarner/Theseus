{-# LANGUAGE AllowAmbiguousTypes #-}

module Theseus.Effect.State where

import Control.Monad.Identity
import Theseus.Eff

data State s m a where
  Get :: State s m s
  Put :: s -> State s m ()

get :: State s `Member` es => Eff ef es s
get = send Get

gets :: State s `Member` es => (s -> a) -> Eff ef es a
gets f = f <$> send Get

put :: State s `Member` es => s -> Eff ef es ()
put = send . Put

modify :: State s `Member` es => (s -> s) -> Eff ef es ()
modify f = get >>= put . f

runState :: ef Identity => s -> Eff ef (State s : es) a -> Eff ef es (s, a)
runState s = handle (pure . (s,)) $ elabState s

elabState :: s -> Handler (State s) ef es ((,) s)
elabState s Get next = runState s $ next $ pure s
elabState _ (Put s') next = runState s' $ next $ pure ()

execState :: ef Identity => s -> Eff ef (State s : es) a -> Eff ef es s
execState s = fmap fst . runState s

evalState :: ef Identity => s -> Eff ef (State s : es) a -> Eff ef es a
evalState s = fmap snd . runState s

interposeState :: (State s `Member` es, ef Identity) => s -> Eff ef es a -> Eff ef es (s, a)
interposeState s = interpose (pure . (s,)) $ elabStateInterpose s

elabStateInterpose :: s -> IHandler (State s) ef es ((,) s)
elabStateInterpose s Get next = interposeState s $ next $ pure s
elabStateInterpose _ (Put s') next = interposeState s' $ next $ pure ()

transactionally :: (State s `Member` es, ef Identity) => Eff ef es a -> Eff ef es a
transactionally @s action = do
  initial <- get @s
  (newS, a) <- interposeState initial action
  put newS
  pure a
