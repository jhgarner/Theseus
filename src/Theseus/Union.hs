{-# LANGUAGE DeepSubsumption #-}
{-# LANGUAGE TypeFamilies #-}

module Theseus.Union (
  Effect,
  Union (This, That),
  Member (inj, getProof),
  prj,
  IsMember (IsMember, Deeper),
  withProof,
) where

import Data.Kind (Constraint, Type)

-- | An Effect is a GADT whose first parameter will be @Eff ef es@ and whose
-- second parameter will be the return type.
type Effect = (Type -> Type) -> Type -> Type

-- An extremely slow open sum.
data Union (ls :: [Effect]) (m :: Type -> Type) (a :: Type) where
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

-- Incoherent because we want the compiler to pick this instance whenever it's
-- not certain what @eff@ is. Once an implementation is chosen on the stack, we
-- do not want to switch to another implementation that happens to handle the
-- same effect. That would make reasoning about code locally much harder.
instance {-# INCOHERENT #-} InternalMember eff es => InternalMember eff (other : es) where
  internalInj eff = That $ internalInj eff

  internalPrj (This _) = Nothing
  internalPrj (That rest) = internalPrj rest

  internalGetProof = Deeper getProof

-- | Proof that some effect is part of the effect stack and will be handled.
-- You probably won't use the functions in this class yourself. Instead, you'll
-- need to carry around this constraint to satisfy functions like `send` and
-- `interpose`
class InternalMember eff es => Member eff es where
  inj :: eff m a -> Union es m a
  getProof :: eff `IsMember` es

data IsMember eff es where
  IsMember :: (forall x. (eff `Member` (eff : es) => x) -> x) -> IsMember eff (eff : es)
  Deeper :: eff `IsMember` es -> IsMember eff (other : es)

withProof :: IsMember eff es -> (eff `Member` es => x) -> x
withProof (IsMember f) x = f x
withProof (Deeper more) x = withProof more x

prj :: InternalMember eff ls => Union ls m a -> Maybe (eff m a)
prj = internalPrj

instance InternalMember eff es => Member eff es where
  inj = internalInj
  getProof = internalGetProof

type family Members (effs :: [Effect]) (es :: [Effect]) :: Constraint where
  Members '[] _ = ()
  Members (a : as) es = (a `Member` es, Members as es)
