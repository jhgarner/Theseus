module Theseus.Effect.Coroutine where

import Control.Monad
import Theseus.Eff

-- # Coroutine

-- The Coroutine effect uses special control flow to pause the thread of
-- computation. While the computation is paused, the interpreters can be
-- changed. It's important though that the thread only be resumed once assuming
-- you want preserve the property that handler ordering doesn't change anything.

-- | Gives you a way to pause the computation until later.
data Coroutine a b m c where
  Yield :: a -> Coroutine a b m b

-- | Pauses the computation providing `a` value and waiting on `b`.
yield :: forall a b lb ub es. Coroutine a b :> es => a -> Eff lb ub es b
yield a = send $ Yield a

-- | Runs a computation until it either completes or pauses. If it pauses, it
-- can be resumed.
runCoroutine :: forall a b c lb ub es. lb (Status lb ub es a b) => Eff lb ub (Coroutine a b : es) c -> Eff lb ub es (Status lb ub es a b c)
runCoroutine = interpretRaw isoSomeId (pure . Done) \(Yield a) _ _ _ next ->
  case evalCf implying (Just $ getProof @(Coroutine a b)) next $ Yielding pure of
    Yielding yielding -> pure $ Yielded a yielding

-- | It is essential that the function provided by `Yielded` be used exactly
-- once. Otherwise you'll get confusing semantics within your code.
data Status lb ub es a b c = Done c | Yielded a (b -> Eff lb ub (Coroutine a b : es) c)
  deriving (Functor)

newtype Yielding b eff m c = Yielding {yielded :: b -> m c}
  deriving (Functor)

instance ControlFlow (Yielding b) Anything where
  Yielding bmc `cfApply` fa = Yielding \b -> bmc b <*> fa
  Yielding bmc `cfBind` afb = Yielding $ bmc >=> afb
  cfOnce ogLb member lifter handler (Yielding @_ @eff go) = Yielding \b -> do
    matchOn (go b) >>= \case
      Pure a -> runIdentityCf $ handler implying member $ IdentityCf @eff a
      Impure eff lb ub lifter' next -> Eff \_ ->
        Impure eff lb ub lifter' $ CfOnce ogLb lifter handler next
  cfPutMeIn _ f (Yielding go) = Yielding \b -> do
    matchOn (go b) >>= \case
      Pure a -> f a
      Impure eff lb ub lifter next -> Eff \_ ->
        Impure eff lb ub lifter $ CfPutMeIn f next
  cfUnrestrict _ bounded ub lb (Yielding bmc) = Yielding $ unrestrict' bounded ub lb . bmc
  cfRaise (Yielding bmc) = Yielding $ raise . bmc
  cfRaiseUnder (Yielding bmc) = Yielding $ raiseUnder . bmc
  cfRun _ handler (Yielding bmc) = Yielding $ handler . bmc
