module Utils (module Utils) where

import Data.Functor
import Test.Hspec as Utils
import Theseus.Eff
import Theseus.Effect.Coroutine

class Expects a b where
  (===) :: a -> (c -> b) -> c -> Expectation

infix 1 ===

instance {-# INCOHERENT #-} (a ~ b, Eq a, Show a) => Expects a b where
  lhs === rhs = (`shouldBe` lhs) . rhs

instance (Eq a, Show a) => Expects a (IO a) where
  lhs === rhs = (`shouldReturn` lhs) . rhs

doneCoroutine :: lb (Status lb ub es a b) => Eff lb ub (Coroutine a b : es) c -> Eff lb ub es c
doneCoroutine action =
  runCoroutine action <&> \case
    Done c -> c
    Yielded _ _ -> error "Coroutine wasn't done"

yieldCoroutine :: lb (Status lb ub es () ()) => Eff lb ub (Coroutine () () : es) c -> Eff lb ub es (Eff lb ub (Coroutine () () : es) c)
yieldCoroutine action =
  runCoroutine action <&> \case
    Yielded () rest -> rest ()
    Done _ -> error "Coroutine was already done"

unitYield :: Coroutine () () :> es => Eff lb ub es ()
unitYield = yield @() @() ()
