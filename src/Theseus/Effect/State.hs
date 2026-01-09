module Theseus.Effect.State where

import Theseus.Eff

-- # State

-- State is a good example of a first order effect that changes the type of its
-- output. It wraps the output in the final state.

-- | Keeps track of some mutable value. Interpreters should follow the "Lens
-- Laws". This means you `Get` back what you `Put`, `Put`ting back what you
-- `Get` does nothing, and `Put`ting twice is the same as `Put`ting once.
data State s m a where
  Get :: State s m s
  Put :: s -> State s m ()

-- | Retrieve the mutable value
get :: State s `Member` es => Eff ef es s
get = send Get

-- | A convience function equivalent to `fmap f get`
gets :: State s `Member` es => (s -> a) -> Eff ef es a
gets f = fmap f get

-- | Sets the mutable state
put :: State s `Member` es => s -> Eff ef es ()
put s = send $ Put s

-- | Uses a function to change the mutable state
modify :: State s `Member` es => (s -> s) -> Eff ef es ()
modify f = get >>= put . f

type StateResult s = ((,) s)

-- | Runs a state effect following the Lens Laws
runState :: ef (StateResult s) => s -> Eff ef (State s : es) a -> Eff ef es (s, a)
runState s =
  -- This is an interpreter which changes the output. Instead of simply
  -- returning `a`, it returns `a` and the final value of the state.
  interpretW_ (s,) \case
    -- Wrapping interpreters need to provide the value to continue with
    -- alongside an interpretation for the next instance of this effect. This
    -- gives us a natural way of keeping track of state.
    Get -> pure (s, runState s)
    Put s' -> pure ((), runState s')

-- | Runs a state using `runState` returning only the final state.
execState :: ef (StateResult s) => s -> Eff ef (State s : es) a -> Eff ef es s
execState s eff = fst <$> runState s eff

-- | Runs a state using `runState` ignoring the final state.
evalState :: ef (StateResult s) => s -> Eff ef (State s : es) a -> Eff ef es a
evalState s eff = snd <$> runState s eff

-- | Keeps track of local state changes and only commits them to the outer
-- state if control flow continues successfully. Something like a `throw` or an
-- `empty` would not commit the transaction.
transactionally :: (State s `Member` es, ef (StateResult s)) => Eff ef (State s : es) a -> Eff ef es a
transactionally action = do
  initial <- get
  (newS, a) <- runState initial action
  put newS
  pure a
