module Theseus.Union (
  Union (This, That),
  Member (inj),
  prj,
  FactfulMaybe (JustFact, NothingFact),
) where

import Data.Kind (Type)

-- An extremely slow open sum. The `c` parameter allows us to remember some
-- facts about the data that were true when we constructed it.
data Union (ls :: [(Type -> Type) -> Type -> Type]) c (m :: Type -> Type) (a :: Type) where
  This :: c eff => eff m a -> Union (eff : ls) c m a
  That :: Union ls c m a -> Union (eff : ls) c m a

class InternalMember eff ls where
  internalInj :: c eff => eff m a -> Union ls c m a
  internalPrj :: Union ls c m a -> FactfulMaybe (c eff) (eff m a)

instance InternalMember eff (eff : es) where
  internalInj = This

  internalPrj (This eff) = JustFact eff
  internalPrj (That _) = NothingFact

instance {-# OVERLAPPABLE #-} InternalMember eff es => InternalMember eff (other : es) where
  internalInj eff = That $ internalInj eff

  internalPrj (This _) = NothingFact
  internalPrj (That rest) = internalPrj rest

class InternalMember eff es => Member eff es where
  inj :: c eff => eff m a -> Union es c m a

-- A Maybe that includes some extra facts in it. The facts (c) probably have
-- something to do with the value stored inside (a).
data FactfulMaybe c a where
  JustFact :: c => a -> FactfulMaybe c a
  NothingFact :: FactfulMaybe c a

prj :: InternalMember eff ls => Union ls c m a -> FactfulMaybe (c eff) (eff m a)
prj = internalPrj

instance InternalMember eff es => Member eff es where
  inj = internalInj
