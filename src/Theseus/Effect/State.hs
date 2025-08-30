{-# LANGUAGE AllowAmbiguousTypes #-}

module Theseus.Effect.State where

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

runState :: s -> Eff ef (State s : es) a -> Eff ef es (s, a)
runState s = handleWrapped sequenceA (s,) (elabState s)

elabState :: s -> HandlerWrapped (State s) ef es ((,) s)
elabState s Get continue = runState s $ continue $ pure s
elabState _ (Put s') continue = runState s' $ continue $ pure ()

execState :: s -> Eff ef (State s : es) a -> Eff ef es s
execState s = fmap fst . runState s

evalState :: s -> Eff ef (State s : es) a -> Eff ef es a
evalState s = fmap snd . runState s

interposeState :: State s `Member` es => s -> Eff ef es a -> Eff ef es (s, a)
interposeState s = interposeWrapped sequenceA (s,) \cases
  Get continue -> interposeState s $ continue $ pure s
  (Put s') continue -> interposeState s' $ continue $ pure ()

transactionally :: State s `Member` es => Eff ef es a -> Eff ef es a
transactionally @s action = do
  initial <- get @s
  (newS, a) <- interposeState initial action
  put newS
  pure a
