{-# LANGUAGE PartialTypeSignatures #-}

module Error where

import Theseus.Eff
import Theseus.Effect.Error
import Theseus.Effect.State
import Utils

testError :: SpecWith ()
testError = do
  describe "Error" do
    it "Should do nothing if no exceptions are thrown" do
      "success" === runEff $ runCatch do
        catch (pure "success") (const undefined)
    it "Should catch exceptions" do
      "failure" === runEff $ runCatch do
        catch (throw ()) (\() -> pure "failure")
    describe "When not recovering" do
      it "Ignores the catching block" do
        Nothing @() === runEff $ runCatchNoRecovery do
          catch (throw ()) (undefined :: () -> _)
    describe "State is preserved past a throw" do
      it "When runCatch happens after runState" do
        ("s2", "failure") === runEff $ runCatch $ runState "s" do
          catch (put "s2" *> throw ()) (\() -> pure "failure")
      it "When runCatch happens before runState" do
        ("s2", "failure") === runEff $ runState "s" $ runCatch do
          catch (put "s2" *> throw ()) (\() -> pure "failure")
