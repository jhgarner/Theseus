module Main (main) where
import Test.Hspec (hspec, describe, it, shouldBe, shouldReturn)
import MyLib
import System.IO.Temp
import Control.Monad.IO.Class

main :: IO ()
main = hspec do
  describe "Empty Eff" do
    it "Should work fine with pure" do
      runEff (pure "test") `shouldBe` "test"
  describe "IO" do
    it "Should handle IO actions correctly" do
        runEffIO (liftIO runTestFile) `shouldReturn` "test"
  describe "Reader" do
    it "must have a working ask method" do
      runEff (runReader "test"  (liftA2 (++) ask ask)) `shouldBe` "testtest"
    it "must have a working local method" do
      runEff (runReader "test"  (local (++ " local") ask)) `shouldBe` "test local"
  where
    runTestFile = writeSystemTempFile "test.txt" "test" >>= readFile
