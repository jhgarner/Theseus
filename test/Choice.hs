module Choice where

import Control.Applicative
import Control.Monad
import Theseus.Eff
import Theseus.Effect.Choice
import Theseus.Effect.Error
import Theseus.Effect.State
import Utils

testChoice :: SpecWith ()
testChoice = do
  describe "Choice" do
    it "runs all permutations" do
      ["ac", "ad", "bc", "bd"] === runEff $ runChoice do
        x <- pure "a" <|> pure "b"
        y <- pure "c" <|> pure "d"
        pure $ x ++ y
    describe "State" do
      -- These tests should show that State will always act in a global way when
      -- composed with Choice. There's no situation where state will branch.
      --
      -- If you want State to branch, you'll need to manage saving and restoring
      -- it at the point of branching.
      it "uses global state when state is outside" do
        -- Sorry this test case is kind of terrifying. The point is that state
        -- keeps growing with each choice.
        ( "[right [right [left [left test left] right] left] right]"
          ,
            [ "[left test left]"
            , "[left [left test left] right]"
            , "[right [left [left test left] right] left]"
            , "[right [right [left [left test left] right] left] right]"
            ]
          )
          === runEff
          $ runState "test"
          $ runChoice @[] do
            prefix <- pure "left" <|> pure "right"
            suffix <- pure "left" <|> pure "right"
            modify \s -> "[" ++ prefix ++ " " ++ s ++ " " ++ suffix ++ "]"
            get
      -- The other handler ordering is a compiler error. Choice must be used
      -- immediately from the top of the stack because it confuses semantics too much
      -- otherwise. This is probably a rule to apply for anything that wants to run
      -- `next` multiple times.
      --
      -- One way to get around that restriction is with the `pauseChoice`
      -- function. It allows you to temporarily collect the various choices
      -- before handing the choices back to whatever implementation you actually
      -- want to use.
      it "supports pausing to add scoped global state" do
        [ ("[left [left test left] right]", "[left test left]")
          , ("[left [left test left] right]", "[left [left test left] right]")
          , ("[right [right test left] right]", "[right test left]")
          , ("[right [right test left] right]", "[right [right test left] right]")
          ]
          === runEff
          $ runCollect @[]
          $ collect do
            prefix <- pure "left" <|> pure "right"
            pauseChoice @[] (runState "test") do
              suffix <- pure "left" <|> pure "right"
              modify \s -> "[" ++ prefix ++ " " ++ s ++ " " ++ suffix ++ "]"
              get
    describe "Catch" do
      it "covers all cases when nothing is thrown" do
        ["a test c", "a test d", "b test c", "b test d"] === runEffDist $ runCollect @[] $ runCatch $ collect do
          prefix <- pure "a" <|> pure "b"
          suffix <-
            unpauseM @[] $ catch
              do collect $ pure "c" <|> pure "d"
              \() -> error "Shouldn't have thrown"
          pure $ prefix ++ " test " ++ suffix
      -- The Semantics Zoo post argues that the following behavior is incorrect
      -- (or at least unintuitive) because some of the alternative branches
      -- vanish. When written out with `unpause` and `collect`, it should be
      -- more clear why this behavior makes sense. Unlike Eff, Theseus won't
      -- distribute the Catch into the branches. Users have to do that
      -- themselves. That'll make the code a little messier, but it'll also make
      -- the behavior more explicit and predictable.
      it "exits early from all branches when an error is thrown" do
        ["a test c", "b test c"] === runEffDist $ runCollect @[] $ runCatch $ collect do
          prefix <- pure "a" <|> pure "b"
          suffix <-
            unpauseM @[] $ catch
              do collect $ throw () <|> pure "d"
              \() -> pure ["c"]
          pure $ prefix ++ " test " ++ suffix

    describe "Coroutine" do
      -- We only need to check when choice is inside. Choice on the outside
      -- won't compile and you can't pass the Status object through pauseChoice.
      it "works when Choice is inside" do
        ["prefix test a", "prefix test b"] === runEffDist $ do
          -- We expect 4 calls to yield
          let handleYields = foldr (>=>) doneCoroutine $ replicate 4 yieldCoroutine
          handleYields $ runChoice @[] do
            suffix <- (unitYield >> pure "a") <|> (unitYield >> pure "b")
            prefix <- unitYield >> pure "prefix"
            pure $ prefix ++ " test " ++ suffix
