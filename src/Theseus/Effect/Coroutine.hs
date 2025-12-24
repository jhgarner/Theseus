module Theseus.Effect.Coroutine where

import Control.Monad
import Theseus.Eff

data Coroutine a b m c where
  Yield :: a -> Coroutine a b m b

yield :: forall a b ef es. Coroutine a b `Member` es => a -> Eff ef es b
yield a = send $ Yield a

runCoroutine :: forall a b c ef es. ef (Status ef es a b) => Eff ef (Coroutine a b : es) c -> Eff ef es (Status ef es a b c)
runCoroutine = handleRaw (pure . Done) \(Yield a) next ->
  case next $ Yielding pure of
    Yielding yielding -> pure $ Yielded a yielding

data Status ef es a b c = Done c | Yielded a (b -> Eff ef (Coroutine a b : es) c)
  deriving (Functor)

newtype Yielding b eff m c = Yielding {yielded :: b -> m c}
  deriving (Functor)

instance ControlFlow (Yielding b) Boring where
  Yielding bmc `cfApply` fa = Yielding \b -> bmc b <*> fa
  Yielding bmc `cfBind` afb = Yielding $ bmc >=> afb
  cfMap _ handler (Yielding bmc) = Yielding $ handler . bmc
  cfRun _ handler (Yielding bmc) = Yielding $ handler . bmc
