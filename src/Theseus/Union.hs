{-# LANGUAGE DeepSubsumption #-}

module Theseus.Union (
  Union (This, That),
  Member (inj, getProof),
  prj,
  IsMember (IsMember, Deeper),
  withProof,
) where

import Data.Kind (Type)

-- An extremely slow open sum.
data Union (ls :: [(Type -> Type) -> Type -> Type]) (m :: Type -> Type) (a :: Type) where
  This :: eff m a -> Union (eff : ls) m a
  That :: Union ls m a -> Union (eff : ls) m a

class InternalMember eff ls where
  internalInj :: eff m a -> Union ls m a
  internalPrj :: Union ls m a -> Maybe (eff m a)
  internalGetProof :: IsMember eff ls

instance InternalMember eff (eff : es) where
  internalInj = This

  internalPrj (This eff) = Just eff
  internalPrj (That _) = Nothing

  internalGetProof = IsMember id

instance {-# INCOHERENT #-} InternalMember eff es => InternalMember eff (other : es) where
  internalInj eff = That $ internalInj eff

  internalPrj (This _) = Nothing
  internalPrj (That rest) = internalPrj rest

  internalGetProof = Deeper getProof

class InternalMember eff es => Member eff es where
  inj :: eff m a -> Union es m a
  getProof :: eff `IsMember` es

data IsMember eff es where
  IsMember :: (forall x. (eff `Member` es => x) -> x) -> IsMember eff es
  Deeper :: eff `IsMember` es -> IsMember eff (other : es)

withProof :: IsMember eff es -> (eff `Member` es => x) -> x
withProof (IsMember f) x = f x
withProof (Deeper more) x = withProof more x

prj :: InternalMember eff ls => Union ls m a -> Maybe (eff m a)
prj = internalPrj

instance InternalMember eff es => Member eff es where
  inj = internalInj
  getProof = internalGetProof
