{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Theseus.Effect.Choice where

import Control.Applicative
import Control.Monad
import Theseus.Eff

data Choice :: Effect where
  Empty :: Choice m a
  -- By constraining Choice to the top of the stack, we guarantee that we'll
  -- always have global state semantics. State can still be used internally, and
  -- you have access to collect and unpause if you need to do something more
  -- complicated.
  Choose :: Choice (Eff ef (Choice : es)) Bool

runChoice ::
  (Alternative f, Traversable f) =>
  Eff ef (Choice : es) a ->
  Eff ef es (f a)
runChoice = handleWrapped sequenceA pure \cases
  Empty _ -> pure empty
  Choose continue ->
    liftA2 (<|>) (runChoice $ continue $ pure True) (runChoice $ continue $ pure False)

pauseChoice ::
  (Pausable into, Collect into `Member` es, Traversable wrap) =>
  (forall a. Eff ef es a -> Eff ef' (Choice : es') (wrap a)) ->
  Eff ef (Choice : es) a ->
  Eff ef' (Choice : es') (wrap a)
pauseChoice @into runners = unpause @into <=< fmap sequenceA . runners . collect @into

instance Alternative (Eff ef (Choice : es)) where
  empty = send Empty
  a <|> b =
    send Choose >>= \case
      True -> a
      False -> b

data Collect into :: Effect where
  Collect :: Eff ef (Choice : es) a -> Collect into (Eff ef es) (into a)

collect :: Collect into `Member` es => Eff ef (Choice : es) a -> Eff ef es (into a)
collect action = send $ Collect action

runCollect :: (Alternative into, Traversable into) => Eff ef (Collect into : es) a -> Eff ef es a
runCollect = handle \(Collect action) continue -> continue $ runChoice action

class Applicative alt => Pausable alt where
  unpause :: alt a -> Eff ef (Choice : es) a

instance Pausable [] where
  unpause [] = empty
  unpause (a : as) = pure a <|> unpause as

instance Pausable Maybe where
  unpause Nothing = empty
  unpause (Just a) = pure a

unpauseM :: Pausable alt => Eff ef es (alt a) -> Eff ef (Choice : es) a
unpauseM @alt = (>>= unpause @alt) . raise
