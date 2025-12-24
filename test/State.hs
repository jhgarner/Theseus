module State where

import Control.Applicative
import Theseus.Eff
import Theseus.Effect.Choice
import Theseus.Effect.Error
import Theseus.Effect.State
import Utils

testState :: SpecWith ()
testState = do
  describe "State" do
    it "tracks updated values" do
      ("newerS", "s test newS") === runEff $ runState "s" do
        s <- get
        put "newS"
        s' <- get
        put "newerS"
        pure $ s ++ " test " ++ s'
    describe "Transaction" do
      it "is invisible when no errors are thrown" do
        ("newerS", "newS test newS") === runEff $ runState "s" $ runCatch do
          catch
            do
              transactionally @String do
                put "newS"
                s <- get
                s' <- get
                put "newerS"
                pure $ s ++ " test " ++ s'
            \() -> error "Nothing should be thrown"
      it "rolls back on error" do
        ("s", "caught newerS") === runEff $ runState "s" $ runCatch do
          catch
            do
              transactionally @String do
                put "newS"
                put "newerS"
                s <- get @String
                throw s
            \s -> pure $ "caught " ++ s
      it "rolls back on empty alternative" do
        ("s", [] @String) === runEff $ runState "s" $ runCollect $ collect do
          transactionally @String do
            put "newS"
            empty

-- TODO transactionally no longer does these things and I think that's fine. It breaks the local reasoning if it worked.
-- it "keeps branches separate" do
--   ("b", ["s -> a test a", "s -> b test b"]) === runEff $ runState "s" $ runCollect $ collect do
--     prefix <- transactionally @String do
--       s <- pure "a" <|> pure "b"
--       startedWith <- get
--       put s
--       pure $ startedWith ++ " -> " ++ s
--     suffix <- get
--     pure $ prefix ++ " test " ++ suffix
-- it "rolls back failed branches" do
--   ("b", ["s -> b test b"]) === runEff $ runState "s" $ runCollect $ collect do
--     prefix <- transactionally @String do
--       s <- pure "a" <|> pure "b"
--       startedWith <- get
--       put s
--       if s == "a" then empty else pure $ startedWith ++ " -> " ++ s
--     suffix <- get
--     pure $ prefix ++ " test " ++ suffix
