module Theseus.Effect.Coroutine where

import Control.Monad
import Theseus.Eff

-- # Coroutine

-- The Coroutine effect uses special control flow to pause the thread of
-- computation. While the computation is paused, the interpreters can be
-- changed. It's important though that the thread only be resumed once assuming
-- you want preserve the property that handler ordering doesn't change anything.

-- | Gives yuo a way to pause the computation until later.
data Coroutine a b m c where
  Yield :: a -> Coroutine a b m b

-- | Pauses the computation providing `a` value and waiting on `b`.
yield :: forall a b ef es. Coroutine a b `Member` es => a -> Eff ef es b
yield a = send $ Yield a

-- | Runs a computation until it either completes or pauses. If it pauses, it
-- can be resumed.
runCoroutine :: forall a b c ef es. ef (Status ef es a b) => Eff ef (Coroutine a b : es) c -> Eff ef es (Status ef es a b c)
runCoroutine = interpretRaw (pure . Done) \(Yield a) _ next ->
  case next $ Yielding pure of
    Yielding yielding -> pure $ Yielded a yielding

-- | It is essential that the function provided by `Yielded` be used exactly
-- once. Otherwise you'll get confusing semantics within your code.
data Status ef es a b c = Done c | Yielded a (b -> Eff ef (Coroutine a b : es) c)
  deriving (Functor)

newtype Yielding b eff m c = Yielding {yielded :: b -> m c}
  deriving (Functor)

instance ControlFlow (Yielding b) Anything where
  Yielding bmc `cfApply` fa = Yielding \b -> bmc b <*> fa
  Yielding bmc `cfBind` afb = Yielding $ bmc >=> afb
  cfMap _ handler (Yielding bmc) = Yielding $ handler . bmc
  cfRun _ handler (Yielding bmc) = Yielding $ handler . bmc
