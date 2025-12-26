{-# LANGUAGE DeepSubsumption #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Theseus.EffType where

import Control.Monad.Identity
import Data.Functor.Combinator
import Data.Kind (Constraint, Type)
import Theseus.Union

class Boring (f :: Type -> Type)
instance Boring f

-- Quantified Constraints are really annoying to have in your type signatures
-- because the compiler gives them extra high priority. For example,
-- ```haskell
-- broken :: (forall w. Traversable w => Monad w) => IO ()
-- broken = getLine >>= putStrLn
-- ```
-- fails to compile because the quantified constraint overrides `IO`'s `Monad`
-- instance. The compiler won't backtrack, so you'll get a compiler error
-- because `IO` doesn't implement `Traversable`.
-- This data type turns the quantified constraint into normal data that the
-- compiler won't try to automatically pass around.
data ef `Implies` c where
  Implies :: (forall x. ((forall w. ef w => c w) => x) -> x) -> ef `Implies` c
implying :: (forall w. ef w => c w) => ef `Implies` c
implying = Implies id

class (forall eff f. Functor f => Functor (cf eff f), r Identity) => ControlFlow cf r | cf -> r where
  cfApply :: Applicative f => cf eff f (a -> b) -> f a -> cf eff f b
  cfBind :: Monad f => cf eff f a -> (a -> f b) -> cf eff f b
  cfMap ::
    (eff `Member` outEs, forall w. ef w => outEf w) =>
    outEf `Implies` r ->
    (forall x. Eff ef es x -> Eff outEf outEs x) ->
    cf eff (Eff ef es) a ->
    cf eff (Eff outEf outEs) a
  cfRun ::
    (eff `Member` es, forall f. ef f => outEf f, r w) =>
    outEf `Implies` r ->
    (forall x. Eff ef es x -> Eff outEf outEs (w x)) ->
    cf eff (Eff ef es) a ->
    cf eff (Eff outEf outEs) (w a)

newtype Eff (ef :: Out) (es :: [Effect]) a = Eff {unEff :: BasicFacts ef -> Freer ef es a}
  deriving (Functor)
  deriving (Applicative, Monad) via ReaderT (BasicFacts ef) (Freer ef es)

-- TODO Figure out how to remove this (and ideally the ef variable) by tracking something else.
data BasicFacts ef where
  Facts :: BasicFacts ef

type Effect = (Type -> Type) -> Type -> Type

type Out = (Type -> Type) -> Constraint

class eff `Member` es => FlipMember es eff
instance eff `Member` es => FlipMember es eff

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
  Impure eff lift next <*> m = Impure eff lift \member x -> next member x `cfApply` Eff (const m)

instance Monad (Freer ef es) where
  Pure ma >>= fmb = fmb ma
  Impure eff lift next >>= fmb = Impure eff lift \member x -> next member x `cfBind` (Eff . const . fmb)

lift :: Union es (Eff ef es) a -> Freer ef es a
lift f = Impure f id \_ x -> x

raise :: forall eff ef es a. Eff ef es a -> Eff ef (eff : es) a
raise (Eff act) = Eff \Facts -> case act Facts of
  Pure a -> pure a
  Impure eff lifter next -> Impure
    (raiseUnion eff)
    ( \case
        Deeper member -> lifter member
        IsMember _ -> error "Raise can't use eff"
    )
    $ \case
      Deeper member -> \x -> withProof member $ cfMap implying raise $ next member x
      -- Why is this impossible? When we raise a value, we know for certain that
      -- it's unused by the computation that's getting raised. That means any
      -- effects must be referencing something deeper. I think the problem comes
      -- from `Member` being an Overlapping class. Imagine we tried to raise an
      -- effect that's already on the stack. All of the `Member` proofs will use
      -- the recursive case to refer down to the original effect skipping over
      -- the newly added one. Although we know that's what will happen, locally
      -- the compiler fears that it'll see a `Member` that doesn't skip the
      -- outermost effect. It can't reason between the function that generates
      -- the constraints and the function that uses them. This is where
      -- `IsMember` comes in. It turns the constraint into a datatype. Whereas
      -- the compiler will throw a compiler error when it has to do this branch,
      -- we can turn it into a runtime error. It is quite unsatisfying that we
      -- can't express this to the compiler. I wonder if there's some machinery
      -- we can use that doesn't make everything gross?
      IsMember _ -> error "Impossible raise condition"

raiseUnion :: Union es (Eff ef esSend) x -> Union (eff : es) (Eff ef esSend) x
raiseUnion (This eff) = That (This eff)
raiseUnion (That rest) = That $ raiseUnion rest

send :: eff `Member` es => eff (Eff ef es) a -> Eff ef es a
send eff = Eff \Facts -> lift $ inj eff
