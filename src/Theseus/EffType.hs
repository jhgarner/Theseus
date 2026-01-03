{-# LANGUAGE DeepSubsumption #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Theseus.EffType where

import Data.Kind (Constraint, Type)
import Theseus.Union

-- | Implementors can control how effectful computations are threaded together.
-- The types that implement ControlFlow are separate from types that are used
-- as Effects. Many Effects can use the same ContrFlow, and a single Effect can
-- be implemented in different ways using different control flows. The vast
-- majority of Effects will use the Identity ControlFlow which threads around
-- a single computation. Some, like Choice, will keep track of multiple
-- computations. Others, like those used by the Throw implementations, ignore
-- some of the computations they receieve and store other information alongside
-- the computation.
class (forall eff f. Functor f => Functor (cf eff f)) => ControlFlow cf r | cf -> r where
  -- | Threads an Applicative operation through the control flow.
  cfApply :: Applicative f => cf eff f (a -> b) -> f a -> cf eff f b

  -- | Threads a Monadic operation through the control flow.
  cfBind :: Monad f => cf eff f a -> (a -> f b) -> cf eff f b

  -- | A heavily restricted version of `hmap` that allows the control flow to
  -- know more about what it's mapping into. The constraints here are a bit
  -- adhoc and unprincipled. Essentially though it means that assumptions you
  -- have about the previous Eff still apply. The implementation for Choice
  -- relies on these.
  cfMap ::
    (eff `Member` outEs, forall w. ef w => outEf w) =>
    outEf `Implies` r ->
    (forall x. Eff ef es x -> Eff outEf outEs x) ->
    cf eff (Eff ef es) a ->
    cf eff (Eff outEf outEs) a

  -- | Another effect's handler needs to be threaded through the control flow.
  -- The handler will wrap the output in some type constrained by @r@. The most
  -- common @r@ is `Anything` because most control flows do not care about the
  -- result. After `Anything` is `Traversable` so that you can partially
  -- inspect whatever is stored within.
  cfRun ::
    (eff `Member` es, forall f. ef f => outEf f, r wrap) =>
    outEf `Implies` r ->
    -- | This parameter must be used linearly. Failing to call it causes
    -- finalizers to not be run. Calling it more than once causes local
    -- reasoning to fail. Since I'm not using the Linear Types extension,
    -- implementors must be careful.
    (forall x. Eff ef es x -> Eff outEf outEs (wrap x)) ->
    cf eff (Eff ef es) a ->
    cf eff (Eff outEf outEs) (wrap a)

-- | Quantified Constraints are really annoying to have in your type signatures
-- because the compiler gives them extra high priority. For example,
--
-- > broken :: (forall w. Traversable w => Monad w) => IO ()
-- > broken = getLine >>= putStrLn
--
-- fails to compile because the quantified constraint overrides `IO`'s `Monad`
-- instance. The compiler won't backtrack, so you'll get a compiler error
-- because `IO` doesn't implement `Traversable`.
--
-- This data type turns the quantified constraint into normal data that the
-- compiler won't try to automatically pass around. By pattern matching and
-- using the provided function, you can pick and choose where the quantified
-- constraint applies.
data ef `Implies` c where
  Implies :: (forall x. ((forall w. ef w => c w) => x) -> x) -> ef `Implies` c

implying :: (forall w. ef w => c w) => ef `Implies` c
implying = Implies id

-- | A class that all types implement. It's mostly helpful when implementing
-- ControlFlow when your control flow type has to restrictions on what it can
-- thread around.
class Anything (f :: Type -> Type)

instance Anything f

-- | An effectful computation. The second type variable stores a list of
-- effects that are valid within the computation. This is common across many
-- effect systems. The first type variable constrains how effects manipulate
-- the return value. This is unique to Theseus.
newtype Eff (ef :: Out) (es :: [Effect]) a = Eff {unEff :: Freer ef es a}
  deriving (Functor, Applicative, Monad)

-- | A constraint on how handlers can manipulate return types. `Anything` and
-- `Traversable` are common.
type Out = (Type -> Type) -> Constraint

-- | A higher order Freer Monad that keeps track of some extra stuff. You
-- shouldn't need to interact with this type. If you're curious about how it
-- works, check out the links in the readme.
data Freer :: Out -> [Effect] -> Type -> Type where
  Pure :: a -> Freer ef es a
  Impure ::
    (Union es (Eff efSend esSend) x) ->
    (forall eff. eff `IsMember` es -> eff `IsMember` esSend) ->
    ( forall g eff someEf.
      (forall a. ef a => someEf a, ControlFlow g someEf) =>
      eff `IsMember` es ->
      g eff (Eff efSend esSend) x ->
      g eff (Eff ef es) a
    ) ->
    Freer ef es a

deriving instance Functor (Freer ef es)

instance Applicative (Freer ef es) where
  pure = Pure

  Pure f <*> rhs = fmap f rhs
  Impure eff lift next <*> m = Impure eff lift \member x -> next member x `cfApply` Eff m

instance Monad (Freer ef es) where
  Pure ma >>= fmb = fmb ma
  Impure eff lift next >>= fmb = Impure eff lift \member x -> next member x `cfBind` (Eff . fmb)

lift :: Union es (Eff ef es) a -> Freer ef es a
lift f = Impure f id \_ x -> x

-- | Adds an extra unused effect onto the top of an effectful computation. This
-- is helpful when you want to hide certain effects from pieces of code.
raise :: forall eff ef es a. Eff ef es a -> Eff ef (eff : es) a
raise (Eff act) = Eff case act of
  Pure a -> pure a
  Impure eff lifter next -> Impure
    (raiseUnion eff)
    ( \case
        Deeper member -> lifter member
        -- Why is this impossible? When we raise a value, we know for certain that
        -- it's unused by the computation that's getting raised. That means any
        -- effects must be referencing something deeper. I think the problem comes
        -- from `Member` being an Overlapping class. Imagine we tried to raise an
        -- effect that's already on the stack. All of the `Member` proofs will use
        -- the recursive case to refer down to the original effect skipping over
        -- the newly added one. Although we know that's what will happen, the
        -- compiler fears that it'll see a `Member` that doesn't skip the
        -- outermost effect. It can't reason between the function that
        -- generates the constraints and the function that uses them. This is
        -- where `IsMember` comes in. It turns the constraint into a datatype.
        -- Whereas the compiler will throw a compiler error when it has to do
        -- this branch, we can turn it into a runtime error. It is quite
        -- unsatisfying that we can't express this to the compiler. I wonder if
        -- there's some machinery we can use that doesn't make everything
        -- gross?
        IsMember _ -> error "Raise can't use eff"
    )
    $ \case
      {- HLINT ignore "Avoid lambda" -}
      Deeper member -> \x -> withProof member $ cfMap implying raise $ next member x
      IsMember _ -> error "Impossible raise condition"

raiseUnion :: Union es (Eff ef esSend) x -> Union (eff : es) (Eff ef esSend) x
raiseUnion (This eff) = That (This eff)
raiseUnion (That rest) = That $ raiseUnion rest

raiseUnder :: forall e eff ef es a. Eff ef (eff : es) a -> Eff ef (eff : e : es) a
raiseUnder (Eff (Pure a)) = Eff $ pure a
raiseUnder (Eff (Impure @_ @_ @esSend eff lifter next)) = Eff $ Impure (raiseUnderUnion eff) lifter' \case
  IsMember _ -> cfMap implying raiseUnder . next getProof
  Deeper (Deeper proof) -> \x -> withProof proof $ cfMap implying raiseUnder $ next (Deeper proof) x
  Deeper (IsMember _) -> error "The raised value is not used"
 where
  lifter' :: (forall someEff. someEff `IsMember` (eff : e : es) -> someEff `IsMember` esSend)
  lifter' l =
    case l of
      IsMember _ -> lifter getProof
      Deeper (Deeper proof) -> lifter $ Deeper proof
      Deeper (IsMember _) -> error "The raised value is not used"

raiseUnderUnion :: Union (eff : es) (Eff efSend esSend) x -> Union (eff : e : es) (Eff efSend esSend) x
raiseUnderUnion (This eff) = This eff
raiseUnderUnion (That rest) = That $ That rest

-- | Perform an effect as long as it will be handled somewhere up the stack.
send :: eff `Member` es => eff (Eff ef es) a -> Eff ef es a
send eff = Eff $ lift $ inj eff
