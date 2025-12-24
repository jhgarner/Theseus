module Reader where

import Control.Applicative
import Theseus.Eff
import Theseus.Effect.Reader
import Utils

testReader :: SpecWith ()
testReader = do
  describe "Reader" do
    it "returns a single value when ask is called" do
      ("test", "test") === runEff $ runReader "test" do liftA2 (,) ask ask
    it "can handle multiple Readers with different types" do
      ("inner", ()) === runEff $ runReader () $ runReader "inner" do liftA2 (,) ask ask
    describe "Local" do
      it "modifies the original value" do
        "test local" === runEff $ runReader "test" do local (++ " local") ask
      it "modifies the original value multiple times" do
        ("test local", "test local") === runEff $ runReader "test" do
          local (++ " local") $ liftA2 (,) ask ask
      it "modifies the original value multiple times even when doing other stuff in between" do
        ("test local", (), "test local") === runEff $ runReader () $ runReader "test" do
          local (++ " local") $ liftA3 (,,) ask ask ask
      it "works when you use the no local reader" do
        ("test", "test") === runEff $ runReaderNoLocal "test" do
          local (++ " local") $ liftA2 (,) ask ask
      it "composes well with coroutines when you swap out the ask" do
        ("first local", "second local") === runEff $ do
          rest <- runReader "first" $ yieldCoroutine do
            local (++ " local") do
              firstAsk <- ask
              unitYield
              lastAsk <- ask
              pure (firstAsk, lastAsk)
          runReader "second" $ doneCoroutine rest
      it "composes poorly when you try to swap local while local is running" do
        -- You could argue that ("first local", "second") would be more correct
        ("first local", "second local") === runEff $ do
          rest <- runReader "first" $ yieldCoroutine do
            local (++ " local") do
              firstAsk <- ask
              unitYield
              lastAsk <- ask
              pure (firstAsk, lastAsk)
          runReaderNoLocal "second" $ doneCoroutine rest
      it "picks up the new local implementation after the current local finishes" do
        ("first local", "second local", "second") === runEff $ do
          rest <- runReader "first" $ yieldCoroutine do
            (first, second) <- local (++ " local") do
              firstAsk <- ask
              unitYield
              lastAsk <- ask
              pure (firstAsk, lastAsk)
            third <- local (++ " never") ask
            pure (first, second, third)
          runReaderNoLocal "second" $ doneCoroutine rest
