module Reader where

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
      it "composes well with coroutines when you swap out the ask" do
        ("first local", "second local") === runEffDist $ do
          rest <- runReader "first" $ yieldCoroutine do
            local (++ " local") do
              firstAsk <- ask
              unitYield
              lastAsk <- ask
              pure (firstAsk, lastAsk)
          runReader "second" $ doneCoroutine rest
      it "composes poorly when you try to swap local while local is running" do
        -- You could argue that ("first local", "second") would be more correct
        ("first local", "second local") === runEffDist $ do
          rest <- runReader "first" $ yieldCoroutine do
            local (++ " local") do
              firstAsk <- ask
              unitYield
              lastAsk <- ask
              pure (firstAsk, lastAsk)
          runReaderNoLocal "second" $ doneCoroutine rest
