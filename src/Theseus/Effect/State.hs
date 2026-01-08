{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Theseus.Effect.State where

import Theseus.Eff

-- # State

-- State is a good example of a first order effect that changes the type of its
-- output. It wraps the output in the final state.

data State s m a where
  Get :: State s m s
  Put :: s -> State s m ()

get :: State s `Member` es => Eff ef es s
get = send Get

gets :: State s `Member` es => (s -> a) -> Eff ef es a
gets f = f <$> send Get

put :: State s `Member` es => s -> Eff ef es ()
put s = send $ Put s

modify :: State s `Member` es => (s -> s) -> Eff ef es ()
modify f = get >>= put . f

type StateResult s = ((,) s)

runState :: ef (StateResult s) => s -> Eff ef (State s : es) a -> Eff ef es (s, a)
runState s =
  interpretW_ (s,) \case
    Get -> pure (s, runState s)
    Put s' -> pure ((), runState s')

execState :: ef (StateResult s) => s -> Eff ef (State s : es) a -> Eff ef es s
execState s eff = fst <$> runState s eff

evalState :: ef (StateResult s) => s -> Eff ef (State s : es) a -> Eff ef es a
evalState s eff = snd <$> runState s eff

-- | Keeps track of local state changes and only commits them to the outer
-- state if control flow continues correctly.
transactionally :: (State s `Member` es, ef (StateResult s)) => Eff ef (State s : es) a -> Eff ef es a
transactionally action = do
  initial <- get
  (newS, a) <- runState initial action
  put newS
  pure a
