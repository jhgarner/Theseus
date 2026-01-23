{-# LANGUAGE PartialTypeSignatures #-}

module Error where

import Theseus.Eff
import Theseus.Effect.Error
import Theseus.Effect.State
import Theseus.Effect.Writer
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
        Nothing @() === runEff $ unrestrict @Traversable @Traversable implying $ runCatchNoRecovery do
          catch (throw ()) (undefined :: () -> _)
    describe "State is preserved past a throw" do
      it "When runCatch happens after runState" do
        ("s2", "failure") === runEff $ runCatch $ runState "s" do
          catch (put "s2" *> throw ()) (\() -> pure "failure")
      it "When runCatch happens before runState" do
        ("s2", "failure") === runEff $ runState "s" $ runCatch do
          catch (put "s2" *> throw ()) (\() -> pure "failure")
    describe "Writes are preserved after a throw" do
      it "When runCatch happens after runWriter" do
        ("1", "failure") === runEff $ runCatch $ runWriter do
          catch (tell "1" *> throw ()) (\() -> pure "failure")
      it "When runCatch happens before runWriter" do
        ("1", "failure") === runEff $ runWriter $ runCatch do
          catch (tell "1" *> throw ()) (\() -> pure "failure")
      it "When the throw is inside a listens block" do
        ("123", "failure") === runEff $ runWriter $ runCatch $ do
          tell "1"
          a <- catch (fmap snd $ listen @String $ tell "2" *> throw ()) (\() -> pure "failure")
          tell "3"
          pure a
      it "But not when inside a pass" do
        ("13", "failure") === runEff $ runWriter $ runCatch $ do
          tell "1"
          a <- catch (fmap snd $ pass @String $ tell "2" *> throw ()) (\() -> pure "failure")
          tell "3"
          pure a
