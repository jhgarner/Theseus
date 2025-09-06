{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Theseus.Effect.Choice where

import Control.Applicative
import Control.Monad
import Data.Distributive (Distributive (distribute))
import Data.Foldable (Foldable (toList))
import Data.Maybe (catMaybes, fromMaybe, mapMaybe)
import Debug.Trace
import Theseus.Eff
import Theseus.Effect.Coroutine
import Unsafe.Coerce (unsafeCoerce)

data Choice :: Effect where
  Empty :: Choice m a
  Choose :: ef Both => String -> Choice (Eff ef es) Bool

data Bush a = Bush [Bush a] | Leaf a
  deriving (Foldable)

showBush :: Int -> Bush a -> String
showBush indent (Leaf a) = replicate (indent * 2) ' ' ++ unsafeCoerce a ++ "()\n"
showBush indent (Bush (x : xs)) = showBush (indent + 1) x ++ showBush indent (Bush xs)
showBush _ (Bush []) = "\n"

traceBush :: String -> Bush a -> Bush a
traceBush tag bush = trace ("\nBush: " ++ tag ++ "\n" ++ showBush 0 bush) bush

bothBush :: Bush (Both a) -> Bush a
bothBush (Leaf (Both a b)) = Bush [Leaf a, Leaf b]
bothBush (Bush ls) = Bush $ fmap bothBush ls

runChoice ::
  (Alternative f, Traversable f) =>
  Eff Distributive (Choice : es) a ->
  Eff Distributive es (f a)
runChoice = runYieldChoice

-- runChoice = fmap (foldl' (\a b -> a <|> pure b) empty) . runChoice'

data ChoiceResult f a = NoSplit a | Split (f (Both a))
  deriving (Functor, Foldable, Traversable)

runChoice' ::
  (Alternative f, Traversable f) =>
  Eff Distributive (Choice : es) a ->
  Eff Distributive es (ChoiceResult f a)
runChoice' @f = handleRaw (fmap sequenceA) (pure . NoSplit) \cases
  Empty _ -> pure $ Split empty
  (Choose _) continue -> do
    a <- runYieldChoice @f $ continue $ pure $ Both True False
    pure $ Split a

runYieldChoice ::
  (Alternative f, Traversable f) =>
  Eff Distributive (Choice : es) a ->
  Eff Distributive es (f a)
runYieldChoice @f eff = do
  statuses <- runChoice' @f $ runCoroutine $ yieldedChoice $ raise @(Coroutine () ()) eff
  case statuses of
    NoSplit (Done a) -> pure $ pure a
    NoSplit _ -> error $ traceShowId "No split happened, but we yielded"
    Split splits -> do
      let (trues, falses) = unzip $ fmap getSplits (toList splits)
      trues <- runChoice @f $ sequenceA trues
      let true = foldl' (\a b -> a <|> pure b) empty $ join $ toList trues
      false <- case falses of
        [] -> pure empty
        a : _ -> runChoice $ runCoroutine a >>= finish
      pure $ true <|> false

headed :: Applicative m => a -> [m a] -> m a
headed def [] = pure def
headed _ (a : _) = a

getSplits :: Both (Status es () () c) -> (Eff Distributive es c, Eff Distributive (Coroutine () () : es) c)
getSplits (Both (Done c) (Yielded () f)) = (pure c, f ())
getSplits (Both (Yielded () c) (Yielded () f)) = (runCoroutine (c ()) >>= finish, f ())

-- getSplits (Both (Yielded () _) (Yielded () f)) = error $ traceShowId "Both didn't look right"

getDone :: Status es a b c -> Maybe c
getDone (Done c) = Just c
getDone _ = Nothing

getYield :: Status es () () c -> Maybe (Eff Distributive es c)
getYield (Yielded () f) = Just $ runCoroutine (f ()) >>= finish
getYield _ = Nothing

finish :: Status es () () c -> Eff Distributive es c
finish (Yielded () f) = runCoroutine (f ()) >>= finish
finish (Done c) = pure c

yieldedChoice ::
  (Choice `Member` es, Coroutine () () `Member` es, ef Both) =>
  Eff ef es a ->
  Eff ef es a
yieldedChoice = interpose \cases
  Empty _ -> send Empty
  (Choose tag) continue -> do
    chose <- send $ Choose tag
    unless chose do yield ()
    yieldedChoice $ continue $ pure chose

halve :: [a] -> [a]
halve ls = take (length ls `div` 2) ls

every :: Int -> [a] -> [a]
every _ [] = []
every n (a : as) = a : every n (drop (n - 1) as)

traceLen :: String -> [a] -> [a]
traceLen prefix ls = trace (prefix ++ ": " ++ show (length ls)) ls

-- liftA2 (<|>) (runChoice $ continue $ pure $ Both True False)

data Both a = Both a a
  deriving (Show, Functor, Foldable, Traversable)

instance Distributive Both where
  distribute boths = Both (fmap fst boths) (fmap snd boths)
   where
    fst (Both a _) = a
    snd (Both _ b) = b

instance Applicative Both where
  pure = error "Don't use applicative both"
  _ <*> _ = error "Bind on both is bad"

pauseChoice ::
  (Pausable into, Collect into `Member` es, Traversable wrap) =>
  (forall a. Eff Distributive es a -> Eff Distributive (Choice : es') (wrap a)) ->
  Eff Distributive (Choice : es) a ->
  Eff Distributive (Choice : es') (wrap a)
pauseChoice @into runners = unpause @into <=< fmap sequenceA . runners . collect @into

instance ef Both => Alternative (Eff ef (Choice : es)) where
  empty = send Empty
  a <|> b =
    send (Choose "Alt") >>= \case
      True -> a
      False -> b

data Collect into :: Effect where
  Collect :: Eff Distributive (Choice : es) a -> Collect into (Eff Distributive es) (into a)

collect :: Collect into `Member` es => Eff Distributive (Choice : es) a -> Eff Distributive es (into a)
collect action = send $ Collect action

runCollect :: (Alternative into, Traversable into) => Eff ef (Collect into : es) a -> Eff ef es a
runCollect = handle \(Collect action) continue -> continue $ runChoice action

class Applicative alt => Pausable alt where
  unpause :: ef Both => alt a -> Eff ef (Choice : es) a

instance Pausable [] where
  unpause [] = empty
  unpause (a : as) = pure a <|> unpause as

instance Pausable Maybe where
  unpause Nothing = empty
  unpause (Just a) = pure a

unpauseM :: Pausable alt => ef Both => Eff ef es (alt a) -> Eff ef (Choice : es) a
unpauseM @alt = (>>= unpause @alt) . raise
