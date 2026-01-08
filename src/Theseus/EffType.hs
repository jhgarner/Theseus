{-# LANGUAGE DeepSubsumption #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Theseus.EffType where

import Data.Kind (Constraint, Type)
import Theseus.Union

-- # Theseus' Core

-- Theseus is a freer-monad based library. We'll cover the freer monad it uses
-- in a moment, but first we need to look at some of the helpers. The first
-- helper is a class which represents the control flow of an effect
-- interpretation.

-- | A constraint on how other interpreters can manipulate return types.
-- `Anything` and `Traversable` are common. `Anything` means that other
-- interpreters can modify te return type any way they want. `Traversable`
-- means other interpreters must keep the return type accessible, although they
-- may change how many of something there are. It might be interesting to try
-- other classes like `Functor` or a theoretical `LinearTraversable`. They
-- haven't come up yet though.
type Out = (Type -> Type) -> Constraint

-- | A higher order Freer Monad that keeps track of some extra stuff. The first
-- type parameter tells us how constrained interpreters are. As you travel down
-- the stack, the constraint can weaken. The final two parameters are the same
-- as other libraries.
data Freer :: Out -> [Effect] -> Type -> Type where
  -- | Pure simply holds a value. You can think of this effect system as
  -- transforming `Impures` over and over again until all that's left is a pure
  -- value. Once a Freer is a pure value, it will no longer be run. This
  -- fact allows finalizers to exist.
  Pure :: a -> Freer ef es a
  -- | Impure is the more interesting case. It looks vaguely like the Freer
  -- Monad suggested by Heftia and the literature it was inspired by.
  Impure ::
    -- This is the effect that was sent. The type variables `efSend`, `esSend`,
    -- and `x` are private and will not change once an `Impure` is constructed.
    -- They represent the state of Freer at the time the effect was sent. `es`
    -- is public. It represents the state of Freer when the effect will be
    -- interpreted. The value that our computation needs to continue running is
    -- of type `x`.
    (Union es (Eff efSend esSend) x) ->
    -- This is a proof that any effects that are in scope when the state is
    -- being interpreted are in scope when the effect was sent. It's equivalent
    -- to the quantified constraint over the `Member` class, but we represent
    -- it with normal values for reasons you'll see later.
    (forall eff. eff `IsMember` es -> eff `IsMember` esSend) ->
    -- Here starts the continuation parameter. This represents the rest of the
    -- computation. The type variables here are `cf` which stands for control
    -- flow (we'll get to that later), `eff` which is the effect we're
    -- interpreting, and `someEf`. The `someEf` parameter (and the `ef`
    -- parameter is general) is confusingly named and I'm not super happy with
    -- it. We'll see how it's used next.
    ( forall cf eff someEf.
      -- These constraints tell us that `cf` can be used as control flow. The
      -- quantified constraint says that whatever constraints that cf needs for
      -- the control flow to work are met by the Freer's first type parameter.
      (ControlFlow cf someEf, forall a. ef a => someEf a) =>
      -- Once again we pass around an explicit proof of `Member`ship. Obviously
      -- the effect we're interpreting is in scope when the interpreter runs.
      -- Using the other membership proof, we can also assume it was in scope
      -- when the effect was sent (which should also be obviously true).
      eff `IsMember` es ->
      -- To continue running, our computation needs an effectful computation
      -- that can run in the same environment as the sent effect returning type
      -- `x`. Note how `efSend`, `esSend`, and `x` are all the private
      -- parameters attached to our effect when it was sent. Wrapping the `x`
      -- in a control flow gives us a lot of power to control what resuming
      -- means. The most common control flow looks like `newtype IdentityCf eff
      -- m x = IdentityCf (m x)`. This is a control flow that simply resumes
      -- the computation once without any extra work.
      cf eff (Eff efSend esSend) x ->
      -- Finally we get the result of passing the next actions through our
      -- control flow.
      cf eff (Eff ef es) a
    ) ->
    Freer ef es a

deriving instance Functor (Freer ef es)

instance Applicative (Freer ef es) where
  pure = Pure

  Pure f <*> rhs = fmap f rhs
  -- The `cfApply` (and the `cfBind` down below) come from the `ControlFlow`
  -- class. We'll discuss them later.
  Impure eff lift next <*> m = Impure eff lift \member x -> next member x `cfApply` Eff m

instance Monad (Freer ef es) where
  Pure ma >>= fmb = fmb ma
  Impure eff lift next >>= fmb = Impure eff lift \member x -> next member x `cfBind` (Eff . fmb)

-- | This adds a single effect to the computation. You can use the `Member`
-- class to convert an effect into a Union, then using `lift` to convert it
-- into a Freer. The `send` function does all this for you so you probably
-- don't need to call lift manually.
lift :: Union es (Eff ef es) a -> Freer ef es a
lift f = Impure f id \_ x -> x

-- There are some other functions for manipulating `Freer`s, but first let's
-- look at the `ControlFlow` class.

-- | This `ControlFlow` class is essential to how Theseus works. When an
-- interpreter wants to resume a computation that paused waiting for a value
-- `a`, it provides the `a`s wrapped in something that implements
-- `ControlFlow`. To be clear, data types that implement ControlFlow are
-- completely different from the data types that represent effects. Many
-- Effects can use the same ContrFlow, and a single Effect can be implemented
-- in different ways using different control flows. The vast majority of
-- Effects will use the Identity ControlFlow which threads around a single
-- computation. Some, like the one used by Choice, will keep track of multiple
-- computations. Others, like those used by the Throw implementations, ignore
-- some of the computations they receieve and store other information alongside
-- the computation.
--
-- `ControlFlow` implementations are very close to higher order functors. This
-- class actually started with HFunctor as a superclass. That changed though so
-- that the ControlFlows could be more specialized and make more assumptions
-- about the functor they contain. In general it's all very adhoc.
class (forall eff f. Functor f => Functor (cf eff f)) => ControlFlow cf r | cf -> r where
  -- | Threads an Applicative operation through the control flow. Alternatively
  -- I could have made ControlFlow a MonadTrans, but the lift operation is kind
  -- of awkward for some of the ControlFlows to implement.
  cfApply :: Applicative f => cf eff f (a -> b) -> f a -> cf eff f b

  -- | Threads a Monadic operation through the control flow.
  cfBind :: Monad f => cf eff f a -> (a -> f b) -> cf eff f b

  -- | A heavily restricted version of `hmap` that allows the control flow to
  -- know more about what it's mapping into. The constraints here are a bit
  -- adhoc and unprincipled. Essentially though it means that assumptions you
  -- have about the previous Eff still apply. The implementation for Choice
  -- relies on these.
  cfMap ::
    -- Regardless of what we're mapping to, It's still valid for the effect
    -- that we're interpreting.
    (eff `Member` outEs, forall w. ef w => outEf w) =>
    -- This is like the other constraints on cfMap, but wrapped in a GADT to
    -- make it easier to work with. The `Implies` type is defined later on.
    outEf `Implies` r ->
    (forall x. Eff ef es x -> Eff outEf outEs x) ->
    cf eff (Eff ef es) a ->
    cf eff (Eff outEf outEs) a

  -- | Another effect's handler needs to be threaded through the control flow.
  -- The handler will wrap the output in some type constrained by `r`. The most
  -- common `r` is `Anything` because most control flows do not care about the
  -- result. Most common after `Anything` is `Traversable` so that you can
  -- partially inspect whatever is stored within.
  cfRun ::
    -- These constraints and first `Implies` parameter accomplish the same
    -- thing as they do for `cfMap`.
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
-- ```haskell
-- broken :: (forall w. Traversable w => Functor w) => IO Int
-- broken = fmap read readLn
-- ```
--
-- fails to compile because the quantified constraint overrides `IO`'s `Functor`
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

-- | Adds an extra unused effect onto the top of an effectful computation. This
-- is helpful when you want to hide certain effects from pieces of code.
raise :: forall eff ef es a. Eff ef es a -> Eff ef (eff : es) a
raise (Eff act) = Eff case act of
  Pure a -> Pure a
  Impure eff lifter next -> Impure
    (raiseUnion eff)
    ( \case
        Deeper member -> lifter member
        -- Why is this impossible? When we raise a value, we know for certain that
        -- it's unused by the computation that's getting raised. That means any
        -- effects must be referencing something deeper. I think the problem comes
        -- from `Member` being an Overlapping class. Imagine we tried to raise an
        -- effect that's already on the stack. All of the `Member` proofs will
        -- use the recursive case to refer down to the original effect skipping
        -- over the newly added one thanks to Incoherent instances. Although we
        -- know that's what will happen, the compiler fears that it'll see
        -- a `Member` that doesn't skip the outermost effect. It can't reason
        -- between the function that generates the constraints and the function
        -- that uses them. This is where `IsMember` comes in. It turns the
        -- constraint into a datatype. Whereas the compiler will throw
        -- a compiler error when it has to do this branch, using a datatype
        -- allows us to defer the error. It is quite unsatisfying that we can't
        -- express this to the compiler. I wonder if there's some machinery we
        -- can use that doesn't make everything gross?
        IsMember _ -> error "Raise can't use eff"
    )
    $ \case
      {- HLINT ignore "Avoid lambda" -}
      Deeper member -> \x -> withProof member $ cfMap implying raise $ next member x
      IsMember _ -> error "Impossible raise condition"

raiseUnion :: Union es (Eff ef esSend) x -> Union (eff : es) (Eff ef esSend) x
raiseUnion (This eff) = That (This eff)
raiseUnion (That rest) = That $ raiseUnion rest

-- | Like the raise function, but inserts the effect one layer deeper in the
-- stack. This allows you to add private effects to the stack.
raiseUnder :: forall e eff ef es a. Eff ef (eff : es) a -> Eff ef (eff : e : es) a
raiseUnder (Eff (Pure a)) = Eff $ pure a
raiseUnder (Eff (Impure @_ @_ @esSend eff lifter next)) = Eff $ Impure (raiseUnderUnion eff) lifter' \case
  IsMember _ -> cfMap implying raiseUnder . next getProof
  Deeper (Deeper proof) -> \x -> withProof proof $ cfMap implying raiseUnder $ next (Deeper proof) x
  Deeper (IsMember _) -> error "2 The raised value is not used"
 where
  lifter' :: (forall someEff. someEff `IsMember` (eff : e : es) -> someEff `IsMember` esSend)
  lifter' l =
    case l of
      IsMember _ -> lifter getProof
      Deeper (Deeper proof) -> lifter $ Deeper proof
      Deeper (IsMember _) -> _

raiseUnderUnion :: Union (eff : es) (Eff efSend esSend) x -> Union (eff : e : es) (Eff efSend esSend) x
raiseUnderUnion (This eff) = This eff
raiseUnderUnion (That rest) = That $ That rest

-- | Perform an effect as long as it will be handled somewhere up the stack.
send :: eff `Member` es => eff (Eff ef es) a -> Eff ef es a
send eff = Eff $ lift $ inj eff

-- | Finishes running an Eff. If your Eff used IO, look in the IO module for
-- the runEffIO function instead. Depending on what other effects you've run,
-- you might need to use `unrestrict` so that the first parameter contains the
-- right constraint.
runEff :: Eff Anything '[] a -> a
runEff (Eff act) = case act of
  Pure a -> a
  Impure a _ _ -> case a of {}
