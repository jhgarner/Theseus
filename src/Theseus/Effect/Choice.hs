{-# OPTIONS_GHC -Wno-orphans #-}

module Theseus.Effect.Choice where

import Control.Applicative
import Control.Monad.Identity
import Theseus.Eff

data Choice :: Effect where
  Empty :: Choice m a
  Choose :: Choice m Bool

runChoice ::
  (Alternative f, ef Identity, Traversable f) =>
  Eff ef (Choice : es) a ->
  Eff ef es (f a)
runChoice = handle (pure . pure) elabNonDet

elabNonDet :: (Alternative f, Traversable f) => Handler Choice ef es f
elabNonDet Empty _ = pure empty
elabNonDet Choose next =
  liftA2 (<|>) (runChoice $ next $ pure True) (runChoice $ next $ pure False)

instance Choice `Member` es => Alternative (Eff ef es) where
  empty = send Empty
  a <|> b =
    send Choose >>= \case
      True -> a
      False -> b
