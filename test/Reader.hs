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
      it "is lexically scoped" do
        "initial" === runEff $ runReader "initial" $ runA $ local (const "local") $ send A
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

data A :: Effect where
  A :: A m String

runA :: (Reader String :> es, lb Identity) => Eff lb ub (A : es) a -> Eff lb ub es a
runA = interpret_ \A -> ask

-- | This is a version of Reader which completely ignores the function passed
-- to local. It's unlawful and you should never use it, but it's convenient
-- for some `Coroutine` tests.
runReaderNoLocal :: lb Identity => r -> Eff lb ub (Reader r : es) a -> Eff lb ub es a
runReaderNoLocal @_ @r r = interpret \sender -> \case
  Ask -> pure $ pure r
  Local _ m -> pure (sender @(Reader r) $ locallyRunReaderNoLocal m)

locallyRunReaderNoLocal :: (Reader r :> es, lb Identity) => Eff lb ub (Reader r : es) a -> Eff lb ub es a
locallyRunReaderNoLocal @r = interpret \sender -> \case
  Ask -> pure <$> ask
  Local _ m -> pure (sender @(Reader r) $ locallyRunReaderNoLocal m)
