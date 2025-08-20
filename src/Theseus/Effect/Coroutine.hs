module Theseus.Effect.Coroutine where

import Data.Distributive
import Theseus.Eff

data Coroutine a b m c where
  Yield :: a -> Coroutine a b m b

yield :: forall a2 a1 ef es. Coroutine a1 a2 `Member` es => a1 -> Eff ef es a2
yield a = send $ Yield a

data Status es a b c = Done c | Yielded a (b -> Eff Distributive (Coroutine a b : es) c)
  deriving (Functor)

runCoroutine :: Eff Distributive (Coroutine a b : es) c -> Eff Distributive es (Status es a b c)
runCoroutine = handle' (pure . Done) elabCoroutine

elabCoroutine :: Handler (Coroutine a b) Distributive es (Status es a b)
elabCoroutine (Yield a) next = pure $ Yielded a (next . pure)
