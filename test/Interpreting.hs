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
      let ea = runEff @([String], Either () ()) $ runOutput @[String] $ runThrow @() $ runA2Throw do
            finally
              do send A2
              do send B2
      ea `shouldBe` (["A", "B"], Left ())
    describe "the final gauntlet" do
      it "Should run all the final blocks once when thrown" do
        let ea = runGauntlet $ runA2Throw do
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
                  output ["Post-finally"]
                do output ["Last one"]
        ea `shouldBe` (["A", "B", "A", "lhs", "rhs", "Last one"], Left ())
      it "should run all the final blocks once when choiced in the body" do
        let ea = runGauntlet $ runA2 do
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
                  output ["Post-finally"]
                do output ["Last one"]
        -- There are 4 "Post-finally"s because there are 4 threads: 2 from the
        -- body of the finally and 2 from the final block.
        ea `shouldBe` (["A", "A", "B", "A", "lhs", "rhs", "Post-finally", "Post-finally", "Post-finally", "Post-finally", "Last one"], Right [(), (), (), ()])
      it "should run all the final blocks once when choiced in an interpreter" do
        let ea = runGauntlet $ runA2Choice do
              finally
                do
                  finally
                    do
                      finally
                        do send A2
                        do send B2
                    do
                      text <- pure "lhs" <|> pure "rhs"
                      output [text]
                  output ["Post-finally"]
                do output ["Last one"]
        -- There are 4 "Post-finally"s because there are 4 threads: 2 from the
        -- body of the finally and 2 from the final block.
        ea `shouldBe` (["Starting A", "A", "A2", "B", "lhs", "rhs", "Post-finally", "Post-finally", "Post-finally", "Post-finally", "Last one"], Right [(), (), (), ()])
  describe "Raise" do
    it "throws no errors when used simply" do
      "s" === runEff $ runReader "s" $ runA (pure "a") $ raise do
        ask
    it "throws no errors when combined with other computations" do
      "a" === runEff $ runReader "s" $ runA (pure "a") $ do
        _ <- send A
        _ <- raise $ ask @String
        send A

runGauntlet :: Eff Traversable Traversable '[Choice, Throw (), Output [String], Collect] () -> ([String], Either () [()])
runGauntlet = runEff @([String], Either () [()]) . unrestrict @Traversable @Traversable implying . runCollect . runOutput @[String] . runThrow @() . collect

data A :: Effect where
  A :: A m String

runA :: lb Identity => Eff lb ub es String -> Eff lb ub (A : es) a -> Eff lb ub es a
runA string = interpret_ \A -> string

data A2 :: Effect where
  A2 :: A2 m ()
  B2 :: A2 m ()

runA2 :: (Output [String] :> es, lb Identity) => Eff lb ub (A2 : es) a -> Eff lb ub es a
runA2 = interpret_ \case
  A2 -> output ["A"]
  B2 -> output ["B"]

runA2Throw :: (Throw () :> es, Output [String] :> es, lb Identity) => Eff lb ub (A2 : es) a -> Eff lb ub es a
runA2Throw = interpret_ \case
  A2 -> output ["A"] >> throw ()
  B2 -> output ["B"]

runA2Choice :: (Choice :> es, Output [String] :> es, lb Identity) => Eff lb ub (A2 : es) a -> Eff lb ub es a
runA2Choice = interpret_ \case
  A2 -> output ["Starting A"] >> (output ["A"] <|> output ["A2"])
  B2 -> output ["B"]
