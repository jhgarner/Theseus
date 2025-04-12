{-# OPTIONS_GHC -Wno-orphans #-}

module Main (main) where
import Test.Hspec (hspec, describe, it, shouldBe, shouldReturn, Expectation)
import MyLib
import System.IO.Temp
import Control.Monad.IO.Class

main :: IO ()
main = hspec do
  describe "Empty Eff" do
    it "Should work fine with pure" do
      "test" === runEff $ pure "test"

  describe "IO" do
    it "Should handle IO actions correctly" do
      "test" === runEffIO $ liftIO do
        writeSystemTempFile "test.txt" "test" >>= readFile

  describe "Reader" do
    it "must have a working ask method" do
      ("test", "test") === runEff $ runReader "test" do liftA2 (,) ask ask
    it "must have a working local method" do
      "test local" === runEff $ runReader "test" do local (++ " local") ask

  describe "State" do
    it "Get without put should act like ask" do
      ("test", "test") === runEff $ evalState "test" do liftA2 (,) get get
    it "Put should apply to the next gets" do
      ("a", "b", "b") === runEff $ evalState "a" do
        a <- get
        put "b"
        b <- get
        c <- get
        pure $ (a, b, c)

class Expects a b where
  (===) :: a -> (c -> b) -> c -> Expectation

infix 1 ===

instance {-# INCOHERENT #-} (a ~ b, Eq a, Show a) => Expects a b where
  lhs === rhs = (`shouldBe` lhs) . rhs

instance (Eq a, Show a) => Expects a (IO a) where
  lhs === rhs = (`shouldReturn` lhs) . rhs
