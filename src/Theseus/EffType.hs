{-# LANGUAGE DeepSubsumption #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Theseus.EffType where

import Data.Kind (Constraint, Type)
import Theseus.Union

-- # Theseus' Core

-- ## Intro

-- Theseus is a freer-monad based library. Before we look at the version of
-- freer that Theseus uses, we'll go over how we get to it.
--
-- The standard first order version of freer looks like
--
-- ```haskell
-- data Freer f a where
--  Pure :: a -> Freer f a
--  Impure :: f x -> (x -> Freer f a) -> Freer f a
-- ```
--
-- The `Pure` case represents the end of an effectful computation. It holds
-- a single value without any effects associated with it. The `Impure` case
-- represents an effectful operation. It holds an effect `f` and
-- a continuation. To interpret the effectful computation, you must use
-- the `f x` to calculate an `x`, then you must pass that `x` to the
-- continuation. Keep doing that recursively on the output of the continuation
-- until you have only a `Pure` value.
--
-- One really cool property I want to point out about this `Freer` is how the
-- `f` never needs to change until it's ready to be interpreted. We drop the
-- `f` into the `Impure` constructor, and until we're ready to interpret it
-- nothing changes. This is different from the `Free` monad where every `bind`
-- operation means calling `map` on the `f` to change it. Not having to change
-- `f` before interpretation is cool because it means we make fewer assumptions
-- about `f`'s structure. At interpretation time we know exactly what `f` is,
-- so it's easy to manipulate. During operations like `bind`, we don't know
-- exactly what `f` is so we have to embed extra information about `f` being
-- a `Functor` for things to work.
--
-- Back to `Freer`, this works great for first order effects, but it can't
-- handle higher order effects. Luckily Heftia proposes a really useful
-- extension of `Freer` which I'll call `HFreer`.
--
-- ```haskell
-- data HFreer f a where
--  Pure :: a -> HFreer f a
--  Impure :: f (HFreer f) x -> (x -> HFreer f a) -> HFreer f a
-- ```
--
-- This is the same as `Freer` except that `f` recursively contains `HFreer`s.
--
-- Those recursive `HFreer`s become a problem for composability: how do we
-- interpret them when we're only interpreting a part of `f`? The
-- interpretation for `f` needs to know exactly which interpreter to use on
-- `HFreer f`. This isn't a huge deal if `f` is something concrete, but it is
-- a problem when you're only interpreting part of `f`. Imagine trying to
-- interpret only the left part of `f :+: g`. We'd like the interpreter for `f`
-- to only care about `f`, but the recursive interpreter needs to handle `f :+:
-- g` which means it needs to handle `g` in some way because the `g`s might
-- contain recursive `HFreer (f :+: g)`s that themselves might contain `f`s
-- that need to be interpreted now.
--
-- One solution to this is to require that all effects be `HFunctor`s. That
-- means all our effects have an `hmap :: forall x. f x -> g x` operation which
-- can be used to recursively apply the interpretation function without
-- worrying about what exactly the effect looks like. That gets us modularity
-- back, but it makes things awkward in a different way. One of the cool things
-- about `Freer` compared to `Free` was how we avoid calling `map` on the `f`s.
-- Now we've kind of added that back by requiring all our `f`s be HFunctors.
--
-- If `Freer` gets around the `map` problem by introducing a continuation and an
-- existential variable, can we do something similar to get around the `hmap`
-- problem? Yes!
--
-- ```haskell
-- data T1Freer f a where
--  Pure :: a -> T1Freer f a
--  Impure :: f (T1Freer g) x -> (forall y. T1Freer g y -> T1Freer f y) -> (x -> T1Freer f a) -> T1Freer f a
-- ```
--
-- We've added an existential `g` variable and a new continuation for handling
-- it. Instead of requiring that the interpreter for `f` recursively call an
-- interpretation function, we pass the interpretation function to the
-- interpreter. Now `f` no longer needs to be an HFunctor! It turns out though
-- that we've limited the kinds of interpreters we can write a lot. All our
-- interpretation functions need to be natural transformations, and many
-- algebraic first order effects don't have natural transformation
-- interpreters. They want to change the return type in some way which isn't
-- allowed. Even if we could make it work, the semantics would also be wonky.
-- The recursive `Freer`s are all being interpreted independently which means
-- things like state will be completely lost between them. I think this is
-- where the weaving comes in for things like Polysemy. The weaving machinery
-- allows effects to weave state between interpreters. I'm going to instead do
-- something slightly different. First I'm going to combine the two
-- continuations into one.
--
-- ```haskell
-- data T2Freer f a where
--  Pure :: a -> T2Freer f a
--  Impure :: f (T2Freer g) x -> (T2Freer g x -> T2Freer f a) -> T2Freer f a
-- ```
--
-- Why do this? One of the problems is that an interpreter for `f` might use
-- the natural transformation a bunch of times on a bunch of computations that
-- return a bunch of different types. What if your interpreter is something
-- like `runThrow` which wants to turn a computation returning `a` into
-- a computation returning `Either e a`? That's not natural so we can't do it.
-- By merging the two continuations, we've limited how the interpretations will
-- be used. The higher order effects can only be interpreted into something
-- returning a type that the caller, not the interpreter, controls. We've
-- limited the kinds of higher order effects you can use, but in exchange we've
-- regained the algebraic effects. On a side note, I think this is pretty close
-- to the subset of higher order effects known as "Scoped Effects" although it
-- might be slightly more powerful.
--
-- At this point we have a well functioning higher order effect system (or at
-- least we should. That version of Theseus wasn't well tested). There are
-- still two problems. First, what if we want something more than scoped
-- effects? Second, isn't it awkward how things like the `Choice` effect
-- interact with state? The latter is a "problem" unrelated to higher order
-- effects. The problem is that the continuation parameter can be used any
-- number of times. If you never call it, you'll skip a bunch of code which
-- might do important things like free resources. If you call it multiple
-- times, you might duplicate operations that aren't idempotent like freeing
-- resources. If algebraic effects compose poorly with resource management,
-- using them will be hard. Somewhat orthogonal to higher order effects,
-- Theseus tries to fix this problem too.
--
-- Theseus introduces a `ControlFlow` types and require that the continuation
-- be called exactly once.
--
-- ```haskell
-- data T3Freer f a where
--  Pure :: a -> T3Freer f a
--  Impure :: f (T3Freer g) x -> (forall cf. ControlFlow cf => cf (T3Freer g) x -> cf (T3Freer f) a) -> T3Freer f a
-- ```
--
-- It might seem like requiring the continuation be called exactly once would
-- break a bunch of algebraic effects, but that's where the `cf` type comes in.
-- The `cf` type turns the control flow of our computation into manipulatable
-- data. The `ControlFlow` class gives `cf` enough information to implement
-- things like `runThrow`, `runCoroutine`, and `runChoice` without dropping or
-- duplicating code that frees resources. Removing all the junk, the
-- `ControlFlow` class could look like
--
-- ```haskell
-- class ControlFlow cf where
--   cfApply :: Applicative f => cf f (a -> b) -> f a -> cf f b
--   cfBind :: Monad f => cf f a -> (a -> f b) -> cf f b
--   cfRun ::
--     (forall x. f x -> g (wrap x)) ->
--     cf f a ->
--     cf g (wrap a)
-- ```
--
-- Concrete control flows might represent a single thread of computation,
-- multiple threads of computation, a paused computation, an aborted
-- computation, a computation that needs to do some other computations on the
-- side, etc. Some of these let you move beyond scoped effects.
--
-- The first two operations in `ControlFlow` allow you to add more computations
-- to the flow. The `cf` decides whether to duplicate those between multiple
-- threads, drop them, or something else. Those operations are required for
-- `Freer` to be a Monad and Applicative.
--
-- The last operation is the really tricky one. Unfortunately the type
-- signature above is far too restrictive for a lot of useful `ControlFlow`s.
-- For example, imagine a `cf` like `newtype MaybeCf f a = MaybeCf (f (Maybe
-- a))`. This represents control flow that has no more than one thread running.
-- When we apply the interpreter given to `cfRun` to the operation in
-- `MaybeCf`, we get an `f (wrap (Maybe a))`. That type can't be used to
-- construct the new `MaybeCf`.
--
-- The solution Theseus adopts is to put restrictions on `wrap`. For `MaybeCf`,
-- it's good enough for `wrap` to implement `Traversable`. That means we can
-- turn a `wrap (Maybe a)` into a `Maybe (wrap a)`. It turns out though that
-- some `wrap`s (like the one returned by a `Coroutine` interpreter) don't
-- implement `Traversable`. To support both `ControlFlow`s that require
-- `Traversable` and interpreters which use values that don't, Theseus makes
-- the constraint on `wrap` flexible. When you're looking at the real
-- implementations, that's what all the `ef` and `r` variables are for.
--
-- Honestly, `ControlFlow` is extremely adhoc in a way that's confusing and
-- unsatisfying. If you're wondering why it looks the way it does, it's
-- probably because things didn't compile or didn't run correctly otherwise.
-- That makes it hard to understand without following a very long journey
-- through bugs and compiler errors. It would be cool if there were something
-- simpler or more fundamental hiding beneath the surface.
--
-- When we get to the real `Freer` monad and `ControlFlow` types that Theseus
-- uses, it'll look more complicated than the one above. Mostly that's also for
-- "boring" adhoc reasons. Things didn't work with the simpler versions, so
-- I added whatever was needed to make them work. I'll try to call those out as
-- we get to them.
--

-- ## The gnarly details

-- | This is the kind of the `ef` and `r` type variables that you see around.
-- It's constraint on how other interpreters can manipulate return types.
-- `Anything` and `Traversable` are common. `Anything` means that other
-- interpreters can modify te return type any way they want. `Traversable`
-- means other interpreters must keep the return type accessible, although they
-- may change how many of something there are. It might be interesting to try
-- other classes like `Functor` or a theoretical `LinearTraversable`. They
-- haven't come up yet though.
type Out = (Type -> Type) -> Constraint

-- | An effectful computation. The second type variable stores a list of
-- effects that are valid within the computation. This is common across many
-- effect systems. The first type variable constrains how effects manipulate
-- the return value. This is unique to Theseus. This type is a newtype wrapper
-- around the Freer type. This was more important in earlier versions of
-- Theseus, but not any more. I'm keeping it around though because having one
-- layer of indirection between the public type everyone uses and the monad
-- that implements it seems nice. When you see `Eff` in a type, treat it as
-- `Freer`.
newtype Eff (ef :: Out) (es :: [Effect]) a
  = Eff {unEff :: Freer ef es a}
  deriving (Functor, Applicative, Monad)

-- | A higher order Freer Monad that keeps track of some extra stuff. The first
-- type parameter tells us how constrained interpreters are. As you travel down
-- the stack, the constraint can weaken. The second is a list of type level
-- effects. The last is the return type of the computation. Usually, a `Freer`
-- type would have just two type parameters and look like `Freer f a` where `f`
-- is some kind of open sum type. I've chosen to instead hardcode this to use
-- an open union because that simplified some of the other bits.
data Freer :: Out -> [Effect] -> Type -> Type where
  -- | Pure simply holds a value. You can think of this effect system as
  -- transforming `Impures` over and over again until all that's left is a pure
  -- value. Once a Freer is a pure value, it will no longer be run. This
  -- fact allows finalizers to exist.
  Pure :: a -> Freer ef es a
  Impure ::
    -- This is the `f` variable from the intro, but I've hardcoded `f` to
    -- a `Union`. I tried making it generic, but it was kind of unwieldy. The
    -- type variables `efSend`, `esSend`, and `x` are existential and will not
    -- change once an `Impure` is constructed. They represent the state of
    -- Freer at the time the effect was sent. `es` is not existential. It
    -- represents the state of Freer when the effect is being interpreted. The
    -- value that our computation needs to continue running is of type `x`.
    -- When an effect is first sent, the *send variables will be the same as
    -- the other variables. That will change as effects are interpreted.
    (Union es (Eff efSend esSend) x) ->
    -- This parameter was not in the introduction above. It is a proof that any
    -- effects that are in scope when the state is being interpreted are in
    -- scope when the effect is sent. It's equivalent to a quantified
    -- constraint over the `Member` class, but we represent it with normal
    -- values for reasons you'll see later.
    (forall eff. eff `IsMember` es -> eff `IsMember` esSend) ->
    -- Here starts the continuation parameter. This represents the rest of the
    -- computation. The type variables here are `cf` which stands for control
    -- flow, `eff` which is the effect we're interpreting, and `r` which is the
    -- constraint that the control flow puts on other interpreters. These all
    -- combine to say that the continuation works with any control flow.
    ( forall cf eff r.
      -- These constraints tell us that `cf` is a control flow. The quantified
      -- constraint says that we can satisfy `cf`'s requirements using whatever
      -- `ef` is.
      (ControlFlow cf r, forall y. ef y => r y) =>
      -- Once again we pass around an explicit proof of `Member`ship. Since the
      -- effect we're interpreting is in scope when the interpreter runs, we
      -- can also assume it is in scope when the effect is sent. This isn't
      -- normally included in `freer` types, but it's practically very useful.
      eff `IsMember` es ->
      -- Finally we have the parameter and return type for the continuation
      -- that we saw in the introduction (although specialized for Freer/Eff)
      cf eff (Eff efSend esSend) x ->
      cf eff (Eff ef es) a
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

-- | This adds a single effect to the computation. You can use the `Member`
-- class to convert an effect into a Union, then using `lift` to convert it
-- into a Freer. The `send` function does all this for you so you probably
-- don't need to call lift manually.
lift :: Union es (Eff ef es) a -> Freer ef es a
lift f = Impure f id \_ x -> x

-- There are some other functions for manipulating `Freer`s, but first let's
-- look at the real `ControlFlow` class.

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
--
-- The `r` parameter is the constraint `cf` puts on `wrap` in `cfRun`. In
-- `Freer`, it's tracked by the `ef` variable.
class (forall eff f. Functor f => Functor (cf eff f)) => ControlFlow cf r | cf -> r where
  cfApply :: Applicative f => cf eff f (a -> b) -> f a -> cf eff f b
  cfBind :: Monad f => cf eff f a -> (a -> f b) -> cf eff f b

  -- This function wasn't included in the introduction because it's mostly just
  -- a tool for type tetris. It gives us a way of manipulating the `ef` and
  -- `es` parameters when we aren't interpreting effects.
  cfMap ::
    (eff `Member` outEs, forall w. ef w => outEf w) =>
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
    -- These constraints and the first `Implies` parameter tell the `cf` that
    -- we're not doing anything to the `ef` and `es` variables that an
    -- interpreter wouldn't do. I don't like this very much, but I'm not sure
    -- what a better option looks like.
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

-- | Adds an extra unused effect onto the top of an effectful computation. This
-- is helpful when you want to hide certain effects from pieces of code. For example,
-- if you specialize it to
-- ``raise :: X `Member` es => Eff ef (X : es) -> Eff ef es a``, then any uses
-- of `X` in the input will use the inner interpreter for `X` instead of the
-- outermost one.
raise :: Eff ef es a -> Eff ef (eff : es) a
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
 where
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
  Deeper (IsMember _) -> error "Impossible raiseUnder + membership proof"
 where
  lifter' :: (forall someEff. someEff `IsMember` (eff : e : es) -> someEff `IsMember` esSend)
  lifter' l =
    case l of
      IsMember _ -> lifter getProof
      Deeper (Deeper proof) -> lifter $ Deeper proof
      -- The `raiseUnder` function is a bit different from `raise` in that it's
      -- easy to trigger this runtime error. If you create a private effect and
      -- try to send it to the sender, that will fail. This makes sense because
      -- the private effect is only in es, not esSend.
      Deeper (IsMember _) -> error "In higher order effects, private effects cannot be run by the sender."

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
