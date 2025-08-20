{-# OPTIONS_GHC -Wno-orphans #-}

module Theseus.Effect.NonDet where

import Control.Applicative
import Control.Monad.Identity
import Theseus.Eff

data NonDet m a where
  Empty :: NonDet m a
  (:<|>) :: m a -> m a -> NonDet m a

runNonDet ::
  (ef Identity, LazyAlternative f, Traversable f) =>
  Eff ef (NonDet : es) a ->
  Eff ef es (f a)
runNonDet = handle (pure . pure) elabNonDet

elabNonDet ::
  (LazyAlternative f, Traversable f) =>
  Handler NonDet ef es f
elabNonDet Empty _ = pure empty
elabNonDet (lhs :<|> rhs) next =
  runNonDet (next lhs) `lazyAlt` runNonDet (next rhs)

class Alternative f => LazyAlternative f where
  lazyAlt :: Monad g => g (f a) -> g (f a) -> g (f a)

instance LazyAlternative [] where
  lazyAlt = liftA2 (<|>)

instance LazyAlternative Maybe where
  lazyAlt ga gb = ga >>= maybe gb (pure . Just)

instance NonDet `Member` es => Alternative (Eff ef es) where
  empty = send Empty
  a <|> b = send $ a :<|> b
