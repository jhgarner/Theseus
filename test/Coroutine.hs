{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Coroutine where

import Theseus.Eff
import Theseus.Effect.Coroutine
import Theseus.Effect.Error
import Utils

testCoroutine :: SpecWith ()
testCoroutine = do
  describe "Coroutine" do
    it "can be stopped and restarted" do
      "ab" === runEffDist $ doneCoroutine do
        let Yielded () rest =
              runEffDist $ runCoroutine do
                gotBack <- yield ()
                pure $ gotBack ++ "b"
        rest "a"

    it "Interacts with catch" do
      "bc" === runEffDist $ doneCoroutine do
        let Yielded () rest =
              runEffDist $ runCoroutine $ runCatch do
                got <- catch (yield @String () >> throw ()) (\() -> yield @String ())
                pure $ got ++ "c"
        let Yielded () rest2 = runEffDist $ runCoroutine $ rest "a"
        rest2 "b"
    it "swaps first order effects" do
      "ab" === runEffDist $ runSimple "b" $ doneCoroutine do
        let rest =
              runEffDist $ runSimple "a" $ yieldCoroutine do
                a <- act
                () <- yield ()
                b <- act
                pure $ a ++ b
        rest
    it "swaps first order effects used in higher order effects" do
      "abc" === runEffDist $ runSimple "b" $ runSimpleH "c" $ doneCoroutine do
        let rest =
              runEffDist $ runSimple "a" $ runSimpleH "c" $ yieldCoroutine do
                actH do
                  a <- act
                  () <- yield ()
                  b <- act
                  pure $ a ++ b
        rest

    it "swaps first order effects in higher order effects when the first order effect is handled first" do
      "abc" === runEffDist $ runSimpleH "c" $ runSimple "b" $ doneCoroutine do
        let Yielded () rest =
              runEffDist $ runSimpleH "c" $ runSimple "a" $ runCoroutine do
                actH do
                  a <- act
                  () <- yield ()
                  b <- act
                  pure $ a ++ b
        rest ()

    it "swaps higher order effects after the higher order effect completes" do
      "abcde" === runEffDist $ runSimpleH "e" $ runSimple "b" $ doneCoroutine do
        let Yielded () rest =
              runEffDist $ runSimpleH "c" $ runSimple "a" $ runCoroutine do
                first <- actH do
                  a <- act
                  () <- yield ()
                  b <- act
                  pure $ a ++ b
                second <- actH $ pure "d"
                pure $ first ++ second
        rest ()

    it "swaps higher order effects after the higher order effect completes when first order effects are handled first" do
      "abcde" === runEffDist $ runSimple "b" $ runSimpleH "e" $ doneCoroutine do
        let Yielded () rest =
              runEffDist $ runSimple "a" $ runSimpleH "c" $ runCoroutine do
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
      SHW "bx" "bx" "ay ay[ab]bybxdbx ay" === runEffDist $ runSimple "b" $ runSimpleHWrapping (fmap (++ "x") act) $ doneCoroutine do
        let SHW f s (Yielded () rest) =
              runEffDist $ runSimple "a" $ runSimpleHWrapping (fmap (++ "y") act) $ runCoroutine do
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

act :: Simple `Member` es => Eff ef es String
act = send Act

runSimple :: String -> Eff ef (Simple : es) a -> Eff ef es a
runSimple s = handle \Act continue -> continue $ pure s

data SimpleH :: Effect where
  ActH :: Simple `Member` es => Eff ef es String -> SimpleH (Eff ef es) String

runSimpleH :: String -> Eff ef (SimpleH : es) a -> Eff ef es a
runSimpleH s = handle \(ActH action) continue -> continue $ fmap (++ s) action

runSimpleHWrapping :: Simple `Member` es => (forall ef es. Simple `Member` es => Eff ef es String) -> Eff ef (SimpleH : es) a -> Eff ef es (SHW a)
runSimpleHWrapping s = handleWrapped sequenceA (SHW "" "") (elabSimpleHWrapping s)

data SHW a = SHW String String a
  deriving (Functor, Foldable, Traversable, Eq, Show)

elabSimpleHWrapping :: Simple `Member` es => (forall ef es. Simple `Member` es => Eff ef es String) -> HandlerWrapped SimpleH ef es SHW
elabSimpleHWrapping s (ActH action) next = do
  fo <- s
  SHW fr sr result <- runSimpleHWrapping s $ next do
    fi <- s
    result <- action
    si <- s
    pure $ fi ++ result ++ si
  so <- s
  pure $ SHW (fo ++ fr) (sr ++ so) result

actH :: (SimpleH `Member` es, Simple `Member` es) => Eff ef es String -> Eff ef es String
actH action = send $ ActH action
