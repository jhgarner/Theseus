module Interpreting where

import Theseus.Eff
import Theseus.Effect.Reader
import Utils

testInterprets :: SpecWith ()
testInterprets = do
  describe "Using" do
    it "allows for private effects" do
      -- TODO I don't know why the compiler is upset when I leave off the `@A`
      -- annotation. It can infer the correct concrete types, but it can't
      -- figure out the `Member A es` constraint. I blame incoherence somehow.
      "s" === runEff $ using @A (runReader "s") (interpret_ (\A -> ask)) do
        send A

data A :: Effect where
  A :: A m String
