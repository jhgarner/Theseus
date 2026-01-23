{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Main (main) where

import Choice (testChoice)
import Control.Exception (ErrorCall (ErrorCall), throwIO, try)
import Control.Monad.IO.Class
import Coroutine (testCoroutine)
import Data.IORef (newIORef, readIORef, writeIORef)
import Error (testError)
import FileExample (testFileExample)
import Interpreting (testInterprets)
import Reader (testReader)
import State (testState)
import System.IO.Temp
import Terminal (testFileThrice, testThrice)
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
    it "should handle exceptions correctly" do
      wasFinallyCalled <- newIORef False
      ea <- try $ runEffIO @() do
        liftIO $ print "before"
        finally
          do
            liftIO $ putStrLn "PreError"
            () <- liftIO (throwIO $ ErrorCall "error")
            liftIO $ putStrLn "PostError"
          do
            liftIO $ putStrLn "Pre final"
            liftIO $ writeIORef wasFinallyCalled True
            liftIO $ putStrLn "Post final"
        liftIO $ print "after all"
      ea `shouldBe` Left (ErrorCall "error")
      readIORef wasFinallyCalled `shouldReturn` True
  it "File Example" do
    testFileExample

  testInterprets
  testReader
  testChoice
  testState
  testWriter
  testError
  testCoroutine
  testThrice
  testFileThrice
