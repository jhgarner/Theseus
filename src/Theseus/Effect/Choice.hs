{-# LANGUAGE QuantifiedConstraints #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Theseus.Effect.Choice where

import Control.Applicative
import Control.Monad
import Control.Monad.Identity
import Theseus.Eff

data Many eff m a where
  Many :: ef [] => ef `Implies` Traversable -> Eff ef es [a] -> (a -> Eff ef es b) -> Many Choice (Eff ef es) b

deriving instance Functor (Many eff m)

instance ControlFlow Many Traversable where
  Many travProof start go `cfApply` fa = Many travProof start ((<*> fa) . go)
  Many travProof start go `cfBind` afb = Many travProof start (go >=> afb)
  cfMap implication handler (Many _ start go) = Many implication (handler start) (handler . go)
  cfRun implication handler (Many travProof start go) = Many implication handledStart pure
   where
    newStart = do
      inits <- start
      results <- traverse (poseChoice travProof . go) inits
      pure $ join results
    handledStart = sequenceA <$> handler newStart

data Choice :: Effect where
  Empty :: Choice (Eff Traversable es) a
  Choose :: Choice (Eff Traversable es) Bool

runChoice ::
  (forall w. Traversable w => ef w) =>
  Eff Traversable (Choice : es) a ->
  Eff ef es [a]
runChoice = interpretRaw (pure . pure) \cases
  Empty _ next ->
    case next $ Many implying (pure []) pure of
      Many travProof start go ->
        join <$> runChoice do
          inits <- start
          results <- traverse (poseChoice travProof . go) inits
          pure $ join results
  Choose _ next ->
    case next $ Many implying (pure [True, False]) pure of
      Many travProof start go ->
        join <$> runChoice do
          inits <- start
          results <- traverse (poseChoice travProof . go) inits
          pure $ join results

poseChoice ::
  (ef [], Choice `Member` es) =>
  ef `Implies` Traversable ->
  Eff ef es a ->
  Eff ef es [a]
poseChoice (Implies traversable) = interposeRaw pure \cases
  Empty _ next ->
    case traversable $ next $ Many implying (pure []) pure of
      many -> runMany many
  Choose _ next ->
    case traversable $ next $ Many implying (pure [True, False]) pure of
      many -> runMany many

runMany :: Choice `Member` es => Many Choice (Eff ef es) a -> Eff ef es [a]
runMany (Many travProof start go) =
  join <$> poseChoice travProof do
    inits <- start
    results <- traverse (poseChoice travProof . go) inits
    pure $ join results

instance Choice `Member` es => Alternative (Eff Traversable es) where
  empty = send Empty
  a <|> b =
    send Choose >>= \case
      True -> a
      False -> b

data Collect :: Effect where
  Collect :: (forall w. Traversable w => ef w) => Eff Traversable (Choice : es) a -> Collect (Eff ef es) [a]

collect :: Collect `Member` es => (forall w. Traversable w => ef w) => Eff Traversable (Choice : es) a -> Eff ef es [a]
collect action = send $ Collect action

runCollect :: ef Identity => Eff ef (Collect : es) a -> Eff ef es a
runCollect = interpret \_ (Collect action) -> pure $ runChoice action
