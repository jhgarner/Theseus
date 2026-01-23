{-# LANGUAGE ImpredicativeTypes #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Coroutine where

import Control.Monad.Identity
import Theseus.Eff
import Theseus.Effect.Coroutine
import Theseus.Effect.Error
import Utils

testCoroutine :: SpecWith ()
testCoroutine = do
  describe "Coroutine" do
    it "can be stopped and restarted" do
      "ab" === runEff $ doneCoroutine do
        let Yielded () rest =
              runEff $ runCoroutine @() @String do
                gotBack <- yield ()
                pure $ gotBack ++ "b"
        rest "a"

    it "Interacts with catch" do
      "bc" === runEff $ doneCoroutine do
        let Yielded () rest =
              runEff $ runCoroutine @() @String $ runCatch do
                got <- catch (yield @() @String () >> throw ()) (\() -> yield @() @String ())
                pure $ got ++ "c"
        let Yielded () rest2 = runEff $ runCoroutine $ rest "a"
        rest2 "b"
    it "swaps first order effects" do
      "ab" === runEff $ runSimple "b" $ doneCoroutine do
        let rest =
              runEff $ runSimple "a" $ yieldCoroutine do
                a <- act
                () <- yield ()
                b <- act
                pure $ a ++ b
        rest
    it "swaps first order effects used in higher order effects" do
      "abc" === runEff $ runSimple "b" $ runSimpleH "c" $ doneCoroutine do
        let rest =
              runEff $ runSimple "a" $ runSimpleH "c" $ yieldCoroutine do
                actH do
                  a <- act
                  () <- yield ()
                  b <- act
                  pure $ a ++ b
        rest

    it "swaps first order effects in higher order effects when the first order effect is handled first" do
      "abc" === runEff $ runSimpleH "c" $ runSimple "b" $ doneCoroutine do
        let Yielded () rest =
              runEff $ runSimpleH "c" $ runSimple "a" $ runCoroutine @() @() do
                actH do
                  a <- act
                  () <- yield ()
                  b <- act
                  pure $ a ++ b
        rest ()

    it "swaps higher order effects after the higher order effect completes" do
      "abcde" === runEff $ runSimpleH "e" $ runSimple "b" $ doneCoroutine do
        let Yielded () rest =
              runEff $ runSimpleH "c" $ runSimple "a" $ runCoroutine @() @() do
                first <- actH do
                  a <- act
                  () <- yield ()
                  b <- act
                  pure $ a ++ b
                second <- actH $ pure "d"
                pure $ first ++ second
        rest ()

    it "swaps higher order effects after the higher order effect completes when first order effects are handled first" do
      "abcde" === runEff $ runSimple "b" $ runSimpleH "e" $ doneCoroutine do
        let Yielded () rest =
              runEff $ runSimple "a" $ runSimpleH "c" $ runCoroutine @() @() do
                first <- actH do
                  a <- act
                  () <- yield ()
                  b <- act
                  pure $ a ++ b
                second <- actH $ pure "d"
                pure $ first ++ second
        rest ()
    it "swaps effects in complicated ways" do
      -- This test is kind of gross and hard to follow, but it shows how effects
      -- can be swapped in in nontrivial ways.
      SHW "bx" "bx" "ay ay[ab]bybxdbx ay" === runEff $ runSimple "b" $ runSimpleHWrapping (fmap (++ "x") act) $ doneCoroutine do
        let SHW f s (Yielded () rest) =
              runEff $ runSimple "a" $ runSimpleHWrapping (fmap (++ "y") act) $ runCoroutine @() @() do
                first <- actH do
                  a <- act
                  () <- yield ()
                  b <- act
                  pure $ "[" ++ a ++ b ++ "]"
                second <- actH $ pure "d"
                pure $ first ++ second
        result <- rest ()
        pure $ f ++ " " ++ result ++ " " ++ s

data Simple :: Effect where
  Act :: Simple m String

act :: Simple :> es => Eff lb ub es String
act = send Act

runSimple :: lb Identity => String -> Eff lb ub (Simple : es) a -> Eff lb ub es a
runSimple s = interpret \_ Act -> pure $ pure s

data SimpleH :: Effect where
  ActH :: Simple :> es => Eff lb ub es String -> SimpleH (Eff lb ub es) String

runSimpleH :: lb Identity => String -> Eff lb ub (SimpleH : es) a -> Eff lb ub es a
runSimpleH s = interpret \_ (ActH action) -> pure $ fmap (++ s) action

runSimpleHWrapping :: Simple :> es => lb SHW => (forall lb ub es. Simple :> es => Eff lb ub es String) -> Eff lb ub (SimpleH : es) a -> Eff lb ub es (SHW a)
runSimpleHWrapping s = interpretW (pure . SHW "" "") (elabSimpleHWrapping s)

data SHW a = SHW String String a
  deriving (Functor, Foldable, Traversable, Eq, Show)

elabSimpleHWrapping :: lb SHW => Simple :> es => (forall lb ub es. Simple :> es => Eff lb ub es String) -> HandlerW SimpleH lb ub es SHW
elabSimpleHWrapping s _ (ActH action) =
  ( pure
      do
        fi <- s
        result <- action
        si <- s
        pure $ fi ++ result ++ si
  , \act -> do
      fo <- s
      SHW fr sr result <- runSimpleHWrapping s act
      so <- s
      pure $ SHW (fo ++ fr) (sr ++ so) result
  )

actH :: (SimpleH :> es, Simple :> es) => Eff lb ub es String -> Eff lb ub es String
actH action = send $ ActH action
