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
        ("s", [] @String) === runEffDist $ runState "s" $ runCollect @[] $ collect do
          transactionally @String do
            put "newS"
            empty
      it "keeps branches separate" do
        ("b", ["s -> a test a", "s -> b test b"]) === runEffDist $ runState "s" $ runCollect @[] $ collect do
          prefix <- transactionally @String do
            s <- pure "a" <|> pure "b"
            startedWith <- get
            put s
            pure $ startedWith ++ " -> " ++ s
          suffix <- get
          pure $ prefix ++ " test " ++ suffix
      it "rolls back failed branches" do
        ("b", ["s -> b test b"]) === runEffDist $ runState "s" $ runCollect @[] $ collect do
          prefix <- transactionally @String do
            s <- pure "a" <|> pure "b"
            startedWith <- get
            put s
            if s == "a" then empty else pure $ startedWith ++ " -> " ++ s
          suffix <- get
          pure $ prefix ++ " test " ++ suffix
      it "can join together multiple branches" do
        ("b", ["s -> a test b", "a -> b test b"]) === runEffDist $ runState "s" $ runCollect @[] $ collect do
          prefix <- transactionally @String $ unpauseM @[] $ collect do
            s <- pure "a" <|> pure "b"
            startedWith <- get
            put s
            pure $ startedWith ++ " -> " ++ s
          suffix <- get
          pure $ prefix ++ " test " ++ suffix
      it "does not roll back if only one branch fails when pausing" do
        ("b", ["a -> b test b"]) === runEffDist $ runState "s" $ runCollect @[] $ collect do
          prefix <- transactionally @String $ unpauseM @[] $ collect do
            s <- pure "a" <|> pure "b"
            startedWith <- get
            put s
            if s == "a" then empty else pure $ startedWith ++ " -> " ++ s
          suffix <- get
          pure $ prefix ++ " test " ++ suffix
      it "rolls back if all the branches fail when pausing" do
        ("s", []) === runEffDist $ runState "s" $ runCollect @[] $ collect do
          prefix <- transactionally @String $ unpauseM @[] $ collect do
            s <- pure "a" <|> pure "b"
            startedWith <- get
            put s
            if s == "a" || s == "b" then empty else pure $ startedWith ++ " -> " ++ s
          suffix <- get
          pure $ prefix ++ " test " ++ suffix
