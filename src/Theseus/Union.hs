module Theseus.Union (
  Union (This, That),
  Member (inj),
  prj,
) where

import Data.Kind (Type)

data Union (ls :: [(Type -> Type) -> Type -> Type]) (m :: Type -> Type) (a :: Type) where
  This :: eff m a -> Union (eff : ls) m a
  That :: Union ls m a -> Union (eff : ls) m a

class InternalMember eff ls where
  internalInj :: eff m a -> Union ls m a
  internalPrj :: Union ls m a -> Maybe (eff m a)

instance InternalMember eff (eff : es) where
  internalInj = This

  internalPrj (This eff) = Just eff
  internalPrj (That _) = Nothing

instance {-# OVERLAPPABLE #-} InternalMember eff es => InternalMember eff (other : es) where
  internalInj eff = That $ internalInj eff

  internalPrj (This _) = Nothing
  internalPrj (That rest) = internalPrj rest

class InternalMember eff es => Member eff es where
  inj :: eff m a -> Union es m a

prj :: InternalMember eff ls => Union ls m a -> Maybe (eff m a)
prj = internalPrj

instance InternalMember eff es => Member eff es where
  inj = internalInj
