{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeepSubsumption #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Theseus.Constraints where

import Data.Coerce
import Data.Kind

-- # Constraints

-- This module is only loosely related to the rest of Theseus. Theseus used to
-- heavily rely on quantified constraints, but those were really difficult to
-- work with. This module defines a bunch of classes and types which emulate
-- quantified constraints in a less principled but practical way.

-- | A natural transformation. Aka we can convert any f into some g
type f ~> g = forall a. f a -> g a

-- | A class that all types implement. It's mostly helpful when implementing
-- ControlFlow when your control flow type has to restrictions on what it can
-- thread around.
class Anything (f :: Type -> Type)

instance Anything f

-- | A class that no types implement. It acts as a useful upper bound because
-- it implies all other classes.
class Nonthing (f :: Type -> Type) where
  produceIt :: a -> f b
  consumeIt :: f a -> b

-- | Proof that two types are the equivalent. If you construct an instance of
-- this type, please make sure the isomorphism holds. For example, `Iso (const
-- Nothing) (const Nothing)` would be a bad `Iso`. It's better to use the
-- functions in this module than it is to call the `Iso` constructor directly.
data f `Iso` g = Iso (f ~> g) (g ~> f)

-- | Types are equivalent to themselves.
idIso :: f `Iso` f
idIso = Iso id id

-- | Newtypes are equivalent to the things they wrap.
newtypeIso :: (forall a. Coercible (f a) (g a)) => f `Iso` g
newtypeIso = Iso coerce coerce

-- | `Iso` is symmetric
flipIso :: f `Iso` g -> g `Iso` f
flipIso (Iso fg gf) = Iso gf fg

-- | `Iso` is transitive
transIso :: f `Iso` g -> g `Iso` h -> f `Iso` h
transIso (Iso fg gf) (Iso gh hg) = Iso (gh . fg) (gf . hg)

-- | Given that some type `f` implements `stronger`, it must also implement
-- `weaker`. For example, ``Applicative `Implies` Functor`` works because every
-- `Applicative` also implements `Functor`. This is very similar to
-- a quantified constraint. Quantified constraints though are really annoying
-- to have in your type signatures because the compiler gives them extra high
-- priority. For example,
--
-- ```haskell
-- broken :: (forall w. Traversable w => Functor w) => IO Int
-- broken = fmap read readLn
-- ```
--
-- fails to compile because the quantified constraint overrides `IO`'s `Functor`
-- instance. The compiler won't backtrack, so you'll get a compiler error
-- because `IO` doesn't implement `Traversable`. Trying to work around this
-- behavior is incredibly gross, so we use `Implies` instead.
data stronger `Implies` weaker where
  -- | Given some `f` that implements `stronger`, you can get some `g` that
  -- implements `weaker`. The `g` might be the same as `f`, or it might be some
  -- newtype if `stronger` and `weaker` weren't designed with each other in
  -- mind even though they could have been. For example, `Monad` implies `Bind`
  -- (`Bind` from the semigroupoids package), but you need the `WrappedMonad`
  -- newtype to show that because base Haskell can't depend on semigroupoids.
  Implies ::
    ( forall f a.
      stronger f =>
      (forall g. weaker g => f `Iso` g -> a) -> a
    ) ->
    stronger `Implies` weaker

-- | Constraints imply themselves
idImply :: ef `Implies` ef
idImply = implying

-- | Implies is equivalent to a quantified constraint
implying :: (forall w. ef w => c w) => ef `Implies` c
implying = Implies \f -> f idIso

-- | Implication is transitive
transImply :: a `Implies` b -> b `Implies` c -> a `Implies` c
transImply (Implies isoAb) (Implies isoBc) = Implies \f -> isoAb \ab -> isoBc $ f . transIso ab

-- | A constraint version of `Implies`. Its like the quantified constraint
-- `forall a. stronger a => weaker a` but without poisoning your function's
-- instance searching. It's also helpful for classes like `Monad` and `Bind`.
-- `Monad` implies `Bind`, but `Bind` is not a superclass of `Monad`. Instead
-- there's a `WrappedMonad` newtype to witness the relationship. With this
-- class, you can define the orphan instance ``Monad `Implies` Bind``.
class stronger `IsAtLeast` weaker where
  implyAtLeast :: stronger `Implies` weaker

instance lhs `IsAtLeast` Anything where
  implyAtLeast = implying

instance Nonthing `IsAtLeast` Traversable where
  implyAtLeast = Implies \f -> f @[] $ Iso consumeIt produceIt

-- Assuming no one's doing anything bad with `Implies`, this instance should be
-- equivalent to any others that apply, so we can make it incoherent.
instance {-# INCOHERENT #-} same `IsAtLeast` same where
  implyAtLeast = idImply

-- | Proof that `f` implements `c`.
data f `IsoSome` c where
  IsoSome :: c g => f `Iso` g -> f `IsoSome` c

isoSomeId :: c f => f `IsoSome` c
isoSomeId = IsoSome idIso

isoImplying :: f `IsoSome` a -> a `Implies` b -> f `IsoSome` b
isoImplying (IsoSome (Iso fg gf)) (Implies isoAb) = isoAb \(Iso ab ba) -> IsoSome $ Iso (ab . fg) (gf . ba)
