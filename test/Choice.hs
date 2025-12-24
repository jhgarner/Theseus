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

    it "skips empty branches" do
      ["ac", "bc", "bd"] === runEff $ runChoice do
        x <- pure "a" <|> pure "b"
        y <- pure "c" <|> pure "d"
        let result = x ++ y
        if result == "ad" then empty else pure result

    it "doesn't blow up when nesting runChoices" do
      ["az", "ac", "az", "ad", "bz", "bc", "bz", "bd"] === runEff $ runChoice do
        x <- pure "a" <|> pure "b"
        yList <- runChoice do pure "z" <|> raise (pure "c" <|> pure "d")
        y <- asum $ pure <$> yList
        pure $ x ++ y

    -- The following examples show how Choice splits the world for as long as
    -- possible, but briefly reunites the worlds when an inner effect handler
    -- needs to complete. This means that effects act the same whether they're
    -- on the outside of a `runChoice` or on the inside.
    describe "State" do
      -- First we need to define the program we'll be running.
      let program :: forall es. (Choice `Member` es, State String `Member` es) => Eff Traversable es String
          program = do
            prefix <- pure "left" <|> pure "right"
            suffix <- pure "left" <|> pure "right"
            modify \s -> "[" ++ prefix ++ " " ++ s ++ " " ++ suffix ++ "]"
            get

      -- This is what the final State value should be assuming global state
      -- semantics.
      let final = "[right [right [left [left test left] right] left] right]"

      -- The only difference between these two cases is that the state is
      -- returned in a different place. The `program`'s execution is the same
      -- regardless of the order. This is powerful and unique from other
      -- libraries (even first order libraries). The ordering of effects has no
      -- impact on the program being executed; it is only observable to the
      -- code that decides the order.
      it "uses global state when state is outside" do
        ( final
          ,
            [ "[left test left]"
            , "[left [left test left] right]"
            , "[right [left [left test left] right] left]"
            , final
            ]
          )
          === runEff
          $ runState "test"
          $ runChoice program
      it "uses global state when state is inside" do
        [ (final, "[left test left]")
          , (final, "[left [left test left] right]")
          , (final, "[right [left [left test left] right] left]")
          , (final, final)
          ]
          === runEff
          $ runChoice
          $ runState "test" program
    describe "Catch" do
      -- Throw, like State, operates using global semantics. As we'll see, this
      -- means the scoping and behavior matches the syntax tree.
      it "covers all cases when nothing is thrown" do
        ["a test c", "a test d", "b test c", "b test d"] === runEff $ runCollect $ runCatch $ collect do
          prefix <- pure "a" <|> pure "b"
          suffix <- catch
            do pure "c" <|> pure "d"
            \() -> error "Shouldn't have thrown"
          pure $ prefix ++ " test " ++ suffix
    -- The Semantics Zoo post argues that the following behavior is unintuitive
    -- because the `pure "d"` branch vanishes. To understand why that happens,
    -- consider what it means for `catch` (and the `runThrow` it uses) to have
    -- global semantics. The `catch` operates on the result of all paths
    -- together, not each path locally. If any one of the paths throw, it
    -- affects all the paths.
    it "exits early from all inner branches when an error is thrown" do
      ["ac", "bc"] === runEff $ runCollect $ runCatch $ collect do
        x <- pure "a" <|> pure "b"
        y <- catch
          do pure "d" <|> throw ()
          \() -> pure "c"
        pure $ x ++ y

    describe "Coroutine" do
      -- We only have to test Choice on the inside because Choice needs to be
      -- capable of inspecting the intermediate results. The `Status` that
      -- Coroutine returns can't be inspected.
      it "works when Choice is inside" do
        ["prefix test a", "prefix test b"] === runEff $ do
          -- We expect 4 calls to yield
          let handleYields = foldr (>=>) doneCoroutine $ replicate 4 yieldCoroutine
          handleYields $ runChoice do
            suffix <- (unitYield >> pure "a") <|> (unitYield >> pure "b")
            prefix <- unitYield >> pure "prefix"
            pure $ prefix ++ " test " ++ suffix
