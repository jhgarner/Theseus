{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Main (main) where

import Choice (testChoice)
import Control.Monad.IO.Class
import Coroutine (testCoroutine)
import Error (testError)
import Reader (testReader)
import State (testState)
import System.IO.Temp
import Theseus.Eff
import Theseus.Effect.IO
import Utils
import Writer (testWriter)

main :: IO ()
main = hspec do
  describe "Empty Eff" do
    it "should work fine with pure" do
      "test" === runEff $ pure "test"

  describe "IO" do
    it "should handle IO actions correctly" do
      "test" === runEffIO $ liftIO do
        writeSystemTempFile "test.txt" "test" >>= readFile

  testReader
  testChoice
  testState
  testWriter
  testError
  testCoroutine
