{-# LANGUAGE DeepSubsumption #-}
{-# LANGUAGE TypeFamilies #-}

module Theseus.Union (
  Effect,
  Union (This, That),
  (:>) (inj, getProof),
  (:>>),
  prj,
  IsMember (IsMember, Deeper),
  withProof,
  dig,
  digUnder,
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
class InternalMember eff es => eff :> es where
  inj :: eff m a -> Union es m a
  getProof :: eff `IsMember` es

instance InternalMember eff es => eff :> es where
  inj = internalInj
  getProof = internalGetProof

prj :: InternalMember eff ls => Union ls m a -> Maybe (eff m a)
prj = internalPrj

type family (:>>) (effs :: [Effect]) (es :: [Effect]) :: Constraint where
  '[] :>> _ = ()
  (a : as) :>> es = (a :> es, as :>> es)

data IsMember eff es where
  IsMember :: (forall x. (eff :> (eff : es) => x) -> x) -> IsMember eff (eff : es)
  Deeper :: eff `IsMember` es -> IsMember eff (other : es)

dig :: Maybe (eff `IsMember` (e : es)) -> Maybe (eff `IsMember` es)
dig Nothing = Nothing
dig (Just (IsMember _)) = Nothing
dig (Just (Deeper rest)) = Just rest

digUnder :: Maybe (eff `IsMember` (e : eNew : es)) -> Maybe (eff `IsMember` (e : es))
digUnder Nothing = Nothing
digUnder (Just (IsMember _)) = Just getProof
digUnder (Just (Deeper (IsMember _))) = Nothing
digUnder (Just (Deeper (Deeper rest))) = Just $ Deeper rest

withProof :: IsMember eff es -> (eff :> es => x) -> x
withProof (IsMember f) x = f x
withProof (Deeper more) x = withProof more x
