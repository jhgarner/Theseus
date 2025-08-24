{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Main (main) where

import Choice (testChoice)
import Control.Applicative (Alternative (..))
import Control.Monad.IO.Class
import Control.Monad.Identity
import Reader (testReader)
import State (testState)
import System.IO.Temp
import Theseus.Eff
import Theseus.Effect.Choice
import Theseus.Effect.Coroutine
import Theseus.Effect.Error
import Theseus.Effect.IO
import Theseus.Effect.State
import Utils

main :: IO ()
main = hspec do
  testReader
  testChoice
  testState
  describe "Empty Eff" do
    it "Should work fine with pure" do
      "test" === runEff $ pure "test"

  describe "IO" do
    it "Should handle IO actions correctly" do
      "test" === runEffIO $ liftIO do
        writeSystemTempFile "test.txt" "test" >>= readFile

  describe "State" do
    it "Get without put should act like ask" do
      ("test", "test") === runEff $ evalState "test" do liftA2 (,) get get
    it "Put should apply to the next gets" do
      ("a", "b", "b") === runEff $ evalState "a" do
        a <- get
        put "b"
        b <- get
        c <- get
        pure (a, b, c)

  describe "Catching" do
    it "Should do nothing if no exceptions are thrown" do
      "success" === runEff $ runCatch do
        catch (pure "success") (const $ pure "failure")
    it "Should catch exceptions" do
      "failure" === runEff $ runCatch do
        catch (throw ()) (\() -> pure "failure")
    describe "When not recovering" do
      it "Ignores the catching block" do
        Nothing @() === runEff $ runCatchNoRecovery do
          catch (throw ()) (undefined :: () -> _)
    describe "State is preserved past a throw" do
      it "When runCatch happens after runState" do
        ("s2", "failure") === runEff $ runCatch $ runState "s" do
          catch (put "s2" *> throw ()) (\() -> pure "failure")
      it "When runCatch happens before runState" do
        ("s2", "failure") === runEff $ runState "s" $ runCatch do
          catch (put "s2" *> throw ()) (\() -> pure "failure")

  describe "NonDet" do
    it "Evaluates left side for collect" do
      "updated" === runEff $ execState "test" $ runChoice @[] do put "updated" <|> pure ()
    it "Evaluates right side for collect" do
      "updated" === runEff $ execState "test" $ runChoice @[] do pure () <|> put "updated"
    it "Uses global state" do
      "test left right" === runEff $ execState "test" $ runChoice @[] do modify (++ " left") <|> modify (++ " right")

  describe "Coroutine" do
    it "Basically functions" do
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
    -- TODO rewrite these Coroutine tests in a more readable way. They start
    -- alright, but they quickly get bad. Everything after this point was coded
    -- very quickly because I was worried about how this all would work.
    it "Allows simple reinterpretation" do
      "ab" === runEffDist $ runSimple "b" $ doneCoroutine do
        let Yielded () rest =
              runEffDist $ runSimple "a" $ runCoroutine do
                a <- act
                () <- yield ()
                b <- act
                pure $ a ++ b
        rest ()
    it "Allows complex reinterpretation" do
      "ab" === runEffDist $ runCatch $ runSimple "b" $ doneCoroutine do
        let Yielded () rest =
              runEffDist $ runCatch $ runSimple "a" $ runCoroutine do
                catch (pure ()) (\() -> pure ())
                a <- act
                () <- yield ()
                b <- act
                pure $ a ++ b
        rest ()

    it "Allows complexer reinterpretation" do
      "ab" === runEffDist $ runSimple "b" $ runSimpleH "c" $ doneCoroutine do
        let Yielded () rest =
              runEffDist $ runSimple "a" $ runSimpleH "c" $ runCoroutine do
                _ <- actH $ pure "nope"
                a <- act
                () <- yield ()
                b <- act
                pure $ a ++ b
        rest ()

    it "Allows complexerer reinterpretation" do
      "abc" === runEffDist $ runSimple "b" $ runSimpleH "c" $ doneCoroutine do
        let Yielded () rest =
              runEffDist $ runSimple "a" $ runSimpleH "c" $ runCoroutine do
                actH do
                  a <- act
                  () <- yield ()
                  b <- act
                  pure $ a ++ b
        rest ()

    it "Allows complexererer reinterpretation" do
      "abc" === runEffDist $ runSimpleH "c" $ runSimple "b" $ doneCoroutine do
        let Yielded () rest =
              runEffDist $ runSimpleH "c" $ runSimple "a" $ runCoroutine do
                actH do
                  a <- act
                  () <- yield ()
                  b <- act
                  pure $ a ++ b
        rest ()

    it "Allows complexerererer reinterpretation" do
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

    it "Allows complexererererer reinterpretation" do
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

    it "Allows complexerererererer reinterpretation" do
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

runSimple :: ef Identity => String -> Eff ef (Simple : es) a -> Eff ef es a
runSimple s = fmap runIdentity . runSimple' s

runSimple' :: ef Identity => String -> Eff ef (Simple : es) a -> Eff ef es (Identity a)
runSimple' s = handle (pure . pure) (elabSimple s)

elabSimple :: ef Identity => String -> Handler Simple ef es Identity
elabSimple s Act next = runSimple' s $ next $ pure s

data SimpleH :: Effect where
  ActH :: Simple `Member` es => Eff ef es String -> SimpleH (Eff ef es) String

runSimpleH :: ef Identity => String -> Eff ef (SimpleH : es) a -> Eff ef es a
runSimpleH s = fmap runIdentity . runSimpleH' s

runSimpleH' :: ef Identity => String -> Eff ef (SimpleH : es) a -> Eff ef es (Identity a)
runSimpleH' s = handle (pure . pure) (elabSimpleH s)

elabSimpleH :: ef Identity => String -> Handler SimpleH ef es Identity
elabSimpleH s (ActH action) next = runSimpleH' s $ next $ fmap (++ s) action

runSimpleHWrapping :: (Simple `Member` es, ef Identity) => (forall ef es. Simple `Member` es => Eff ef es String) -> Eff ef (SimpleH : es) a -> Eff ef es (SHW a)
runSimpleHWrapping s = handle (pure . SHW "" "") (elabSimpleHWrapping s)

data SHW a = SHW String String a
  deriving (Functor, Foldable, Traversable, Eq, Show)

elabSimpleHWrapping :: (Simple `Member` es, ef Identity) => (forall ef es. Simple `Member` es => Eff ef es String) -> Handler SimpleH ef es SHW
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
