module Interpreting where

import Theseus.Eff
import Theseus.Effect.Reader
import Utils

testInterprets :: SpecWith ()
testInterprets = do
  describe "Using" do
    it "allows for private effects" do
      "s" === runEff $ using (runReader "s") (runA ask) do
        send A

  describe "Raise" do
    it "throws no errors when used simply" do
      "s" === runEff $ runReader "s" $ runA (pure "a") $ raise do
        ask
    it "throws no errors when combined with other computations" do
      "a" === runEff $ runReader "s" $ runA (pure "a") $ do
        _ <- send A
        _ <- raise $ ask @String
        send A

data A :: Effect where
  A :: A m String

runA :: ef Identity => Eff ef es String -> Eff ef (A : es) a -> Eff ef es a
runA string = interpret_ \A -> string
