module Interpreting where

import Control.Applicative
import Theseus.Eff
import Theseus.Effect.Choice
import Theseus.Effect.Error
import Theseus.Effect.Output
import Theseus.Effect.Reader
import Utils

testInterprets :: SpecWith ()
testInterprets = do
  describe "Using" do
    it "allows for private effects" do
      "s" === runEff $ using (runReader "s") (runA ask) do
        send A

  describe "finally" do
    it "Should run finally even when interpreters throw exceptions" do
      let ea = runEff @([String], Either () ()) $ runOutput @[String] $ runThrow @() $ runA2 do
            finally
              do send A2
              do send B2
      ea `shouldBe` (["A", "B"], Left ())
    it "should survive the final gauntlet" do
      let ea = runEff @([String], Either () [()]) $ unrestrict @Traversable @Traversable implying $ runCollect $ runOutput @[String] $ runThrow @() $ collect $ runA2 do
            finally
              do
                finally
                  do
                    finally
                      do send A2 <|> send A2
                      do send B2 >> send A2
                  do
                    text <- pure "lhs" <|> pure "rhs"
                    output [text]
              do output ["Last one"]
      ea `shouldBe` (["A", "B", "A", "lhs", "rhs", "Last one"], Left ())
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

runA :: lb Identity => Eff lb ub es String -> Eff lb ub (A : es) a -> Eff lb ub es a
runA string = interpret_ \A -> string

data A2 :: Effect where
  A2 :: A2 m ()
  B2 :: A2 m ()

runA2 :: (Throw () :> es, Output [String] :> es, lb Identity) => Eff lb ub (A2 : es) a -> Eff lb ub es a
runA2 = interpret_ \case
  A2 -> output ["A"] >> throw ()
  B2 -> output ["B"]
