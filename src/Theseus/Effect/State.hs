{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}

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

withState :: State s `Member` es => Eff ef es a -> Eff ef es (s, a)
withState eff = do
  a <- eff
  s' <- get
  pure (s', a)

type StateResult s = ((,) s)

evalState :: ef (StateResult s) => s -> Eff ef (State s : es) a -> Eff ef es (s, a)
evalState s =
  handleWrapped (s,) \cases
    Get continue -> evalState s $ continue $ pure s
    (Put s') continue -> evalState s' $ continue $ pure ()

execState :: ef (StateResult s) => s -> Eff ef (State s : es) a -> Eff ef es s
execState s eff = fst <$> evalState s eff

runState :: ef (StateResult s) => s -> Eff ef (State s : es) a -> Eff ef es (s, a)
runState = evalState

interposeState :: (ef (StateResult s), State s `Member` es) => s -> Eff ef es a -> Eff ef es (s, a)
interposeState s = interposeWrapped (s,) \cases
  Get continue -> interposeState s $ continue $ pure s
  (Put s') continue -> interposeState s' $ continue $ pure ()

transactionally :: (State s `Member` es, ef (StateResult s)) => Eff ef es a -> Eff ef es a
transactionally @s action = do
  initial <- get @s
  (newS, a) <- interposeState initial action
  put newS
  pure a
