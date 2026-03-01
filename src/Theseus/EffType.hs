{-# LANGUAGE QuantifiedConstraints #-}

module Theseus.EffType where

import Control.Monad
import Control.Monad.Reader (ReaderT (ReaderT))
import Data.Kind (Constraint, Type)
import Theseus.Constraints
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
-- One really cool property of this `Freer` is how the `f` never needs to
-- change until it's ready to be interpreted. We drop the `f` into the `Impure`
-- constructor, and, until we're ready to interpret, the value stays the same.
-- This is different from the `Free` monad where every `bind` operation means
-- calling `map` on `f`. Not having to change `f` before
-- interpretation is cool because it means we make fewer assumptions about
-- `f`'s structure. At interpretation time we know exactly what `f` is, so it's
-- easy to manipulate. During operations like `bind`, we don't know exactly
-- what `f` is so we have to embed extra information about `f` being
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
-- that need to be interpreted now. That's a messy knot to untangle!
--
-- One solution to this is to require that all effects be `HFunctor`s. That
-- means all our effects have an `hmap :: forall x. f x -> g x` operation which
-- can be used to recursively apply the interpretation function without
-- worrying about what exactly the effect looks like. That gets us modularity
-- back, but it makes things awkward in a different way. One of the cool things
-- about `Freer` compared to `Free` was how we avoided calling `map` on the
-- `f`s. Now we've kind of added that back by requiring all our `f`s be
-- `HFunctor`s.
--
-- If `Freer` gets around the `map` problem by introducing a continuation and an
-- existential variable, can we do something similar to get around the `hmap`
-- problem? Yes!
--
-- ```haskell
-- data T1Freer f a where
--  Pure :: a -> T1Freer f a
--  Impure :: f g x -> (forall y. g y -> T1Freer f y) -> (x -> T1Freer f a) -> T1Freer f a
-- ```
--
-- We've added an existential `g` variable and a new continuation for handling
-- it. Instead of requiring that the interpreter for `f` recursively call an
-- interpretation function, we pass the interpretation function to the
-- interpreter. Now `f` no longer needs to be an HFunctor! In the process
-- though we've severely limited the kinds of interpreters we can write. All
-- our interpretation functions need to be natural transformations, and many
-- algebraic first order effects don't have natural transformation
-- interpreters. Imagine an interpreter like `runThrow` which wants to turn
-- a computation returning `a` into a computation returning `Either e a`.
-- That's not natural so we can't use it. Even if we could make `runThrow`
-- work, the semantics would be wonky. The recursive `Freer`s are all being
-- interpreted independently which means things like state will be completely
-- lost between them. I think this is where the weaving comes in for things
-- like Polysemy. The weaving machinery allows effects to weave state between
-- interpreters. Instead of going in that direction, I'm going to combine the
-- two continuations into one.
--
-- ```haskell
-- data T2Freer f a where
--  Pure :: a -> T2Freer f a
--  Impure :: f g x -> (g x -> T2Freer f a) -> T2Freer f a
-- ```
--
-- Why do this? By merging the two continuations, we've limited how the
-- interpretations will be used. The higher order effects can only be
-- interpreted into something returning a type that the caller, not the
-- interpreter, controls. We've limited the kinds of higher order effects you
-- can use, but in exchange we've regained the algebraic effects. On a side
-- note, I think this is pretty close to the subset of higher order effects
-- known as "Scoped Effects".
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
-- resources. Having to pick between algebraic effects and resource management
-- is bad and many people pick resource management. Although orthogonal to
-- higher order effects, Theseus tries to fix this problem too.
--
-- Theseus solves this by making the continuation inspectable using a `CF`
-- (short for Control Flow) type. Instead of storing a function, we store
-- a `CF` that tracks all the ways the function would have been manipulated.
-- Theseus then requires that `CF` be used linearly by all interpreters.
-- A simplified version looks like the following.
--
-- ```haskell
-- data T3Freer f a where
--  Pure :: a -> T3Freer f a
--  Impure :: f (T3Freer g) x -> (Cf (T3Freer g x) (T3Freer f) a) -> T3Freer f a
--
-- data CF input f a where
--  CfIn :: CF (f a) f a
--  CfBind :: CF input f x -> (x -> f a) -> CF input f a
--  CfRun :: (forall x. f x -> g (wrap x)) -> CF input f a -> CF input g (wrap a) -> CF input f (wrap a)
--  ...
-- ```
--
-- The `CF` type gives us enough information to implement things like
-- `runThrow`, `runCoroutine`, and `runChoice` without dropping or duplicating
-- code that frees resources. Consumers of `CF` might represent a single thread
-- of computation, multiple threads of computation, a paused computation, an
-- aborted computation, a computation that needs to do some other computations
-- on the side, etc. Some of these let you move beyond scoped effects.
-- Consumers look like catamorphisms/folds.
--
-- The first constructor for `CF` is the base case for our tree-like structure.
-- It tells us that the Control Flow simply returns its input. The second
-- allows you to add more computations to the flow. The interpreter decides
-- whether to duplicate those between multiple threads, drop them, or something
-- else.
--
-- The last constructor is the really tricky one. Unfortunately the type
-- signature above is far too restrictive for a lot of useful
-- interpretations. For example, imagine an interpreter for catch which
-- ignores all the catch blocks and simply returns `Nothing` if anything
-- throws. Although it might sound simpler than the normal `Catch`
-- interpretation, it's actually much trickier. It represents control flow that
-- has at most one running thread.  We need the fold to give us a `Freer es
-- (Maybe a)`. When we try to handle `CfRun` though, we'll be stuck with
-- a `Freer es (wrap (Maybe a))`. If the `wrap` is completely opaque, there's
-- no way we can get it back into the correct `Freer es (Maybe (wrap a))`
-- shape.
--
-- The solution Theseus adopts is to put restrictions on `wrap`. For our weird
-- catch, it's good enough for `wrap` to implement `Traversable`. That means we
-- can turn a `wrap (Maybe a)` into a `Maybe (wrap a)` using `sequence`. It
-- turns out though that some `wrap`s (like the one returned by a `Coroutine`
-- interpreter) don't implement `Traversable`. To support both `ControlFlow`s
-- that require `Traversable` and interpreters which use values that don't,
-- Theseus makes the constraint on `wrap` flexible. When you're looking at the
-- real implementations, that's what all the `lb` and `ub` variables are for.
--
-- When you reach the real `CF` type, you'll see much more than the
-- 3 constructors I shared above. Some of them are there to support things like
-- `raise` and others are there to help interpreters remain linear. The real
-- `Freer` type is also more complicated mostly because of those `lb` and `ub`
-- variables. Hopefully this background helps you understand the more
-- complicated bits. I'm always welcome to ideas about how things can be
-- simplified or normalized!

-- ## The gnarly details

-- | This is the kind of the `lb` and `ub` type variables that you will see around.
-- It's a constraint on how other interpreters can manipulate return types.
-- `Anything` and `Traversable` are common. `Anything` means that other
-- interpreters can modify the return type any way they want. `Traversable`
-- means other interpreters must keep the return type accessible, but they may
-- change how many of something there are. It might be interesting to try other
-- classes like `Functor` or a theoretical `LinearTraversable`. They haven't
-- been needed yet though.
type Bound = (Type -> Type) -> Constraint

-- | An effectful computation. The third type variable stores a list of
-- effects that are valid within the computation. This is common across many
-- effect systems. The first two type variables constrain how effects manipulate
-- the return value. Those are unique to Theseus. You can mostly think of `Eff`
-- and `Freer` as interchangable. `Eff` though requires a `Facts` parameter.
-- Why? Interpreters want to rely on the fact that the upper bound implies the
-- lower bound. Since `lb` and `ub` are usually type variables, every single
-- function working with `Eff` would need to add or pass around proof that `ub`
-- implies `lb`. To avoid all that noise, we use a `Reader` pattern. You can
-- construct a nonsense type like `Eff Show Read ...`, but you can't run it.
--
-- I might try adding other useful pieces of information to the `Facts` object.
-- For example, I could require that `Identity` be valid for all `lb`s.
newtype Eff (lb :: Bound) (ub :: Bound) (es :: [Effect]) a
  = Eff {unEff :: Facts lb ub -> Freer lb ub es a}
  deriving (Functor)
  deriving (Applicative, Monad) via ReaderT (Facts lb ub) (Freer lb ub es)

newtype Facts lb ub = Facts {bounded :: ub `Implies` lb}

getFacts :: Eff lb ub es (Facts lb ub)
getFacts = Eff pure

matchOn :: Eff lb ub es a -> Eff lb ub es (Freer lb ub es a)
matchOn (Eff act) = Eff $ pure . act

effUn :: Facts lb ub -> Eff lb ub es a -> Freer lb ub es a
effUn = flip unEff

-- | A higher order Freer Monad that keeps track of some extra stuff. The type
-- parameters match `Eff`. Usually, a `Freer` type would have just two type
-- parameters and look like `Freer f a`. Then somewere else you make `f` into
-- some concrete open union type. Instead I hardcode this to use an open union
-- because that simplified some of the other bits. The extensible effects paper
-- also hardcodes, so I think that's fine.
data Freer :: Bound -> Bound -> [Effect] -> Type -> Type where
  -- | Pure simply holds a value. You can think of Theseus as transforming
  -- `Impures` over and over again until all that's left is a `Pure` value.
  -- Once a Freer is a `Pure` value, it will no longer be run. This fact allows
  -- finalizers to exist.
  Pure :: a -> Freer lb ub es a
  -- | Impure holds an effect that needs to be run before the program can
  -- continue. It holds both the effect and the rest of the program.
  Impure ::
    -- This is the `f` variable from the intro, but I've hardcoded `f` to
    -- a `Union`. I tried making it generic, but it was kind of unwieldy. The
    -- type variables `efSend`, `esSend`, and `x` are existential and will not
    -- change once an `Impure` is constructed. They represent the state of
    -- Freer at the time the effect is sent. `es` is not existential. It
    -- represents the state of Freer when the effect is being interpreted. The
    -- value that our computation needs to continue running is of type `x`.
    -- When an effect is first sent, the *send variables will be the same as
    -- the other variables. That will change as effects are interpreted,
    -- raised, etc.
    Union es (Eff lbSend ubSend esSend) x ->
    -- These three parameters were not in the introduction above. The first
    -- proves that the lower bound has only gotten lower as the program has
    -- run. The second proves that the upper bound has only gotten higher as
    -- the program has run. Together they prove that our bounding constraints
    -- have not contracted. With these proofs, interpreters can know that their
    -- return type changes are valid, and that other interpreters will use
    -- valid return type changes. The third parameter is a proof that effects
    -- that are in scope when the state is being interpreted are in scope when
    -- the effect is being sent. It's convenient when writing interpreters and
    -- intuitively makes sense even if it's sometimes not true. All effects
    -- that haven't been raised will remain in scope.
    lbSend `Implies` lb ->
    ub `Implies` ubSend ->
    (forall eff. eff `IsMember` es -> Maybe (eff `IsMember` esSend)) ->
    -- This is the continuation parameter. Instead of using a plain function
    -- for the continuation, we use a type called `CF` (which stands for
    -- Control Flow). The `CF` type supports everything the continuation needs
    -- to do while being easier to inspect.
    CF (Eff lbSend ubSend esSend x) (Eff lb ub es) a ->
    -- And that's everything for the Freer type! We can implement the Monad
    -- hierarchy on it.
    Freer lb ub es a

deriving instance Functor (Freer lb ub es)

instance Applicative (Freer lb ub es) where
  pure = Pure

  Pure f <*> rhs = fmap f rhs
  Impure eff lb ub lift (CfFmap xab cfx) <*> ma = Impure eff lb ub lift $ CfBind cfx (\x -> xab x <$> Eff (const ma))
  Impure eff lb ub lift (CfApply cfxab mx) <*> ma = Impure eff lb ub lift $ CfBind cfxab (\xab -> xab <$> mx <*> Eff (const ma))
  Impure eff lb ub lift (CfBind cfx xmab) <*> ma = Impure eff lb ub lift $ CfBind cfx (\x -> xmab x <*> Eff (const ma))
  Impure eff lb ub lift next <*> m = Impure eff lb ub lift $ CfApply next (Eff (const m))

instance Monad (Freer lb ub es) where
  Pure ma >>= fmb = fmb ma
  Impure eff lb ub lift (CfFmap f next) >>= fmb = Impure eff lb ub lift $ CfBind next (Eff . const . fmb . f)
  Impure eff lb ub lift (CfApply cfxa mx) >>= amb = Impure eff lb ub lift $ CfBind cfxa $ \xa -> mx >>= Eff . const . amb . xa
  Impure eff lb ub lift (CfBind cfx xma) >>= amb = Impure eff lb ub lift $ CfBind cfx $ xma >=> Eff . const . amb
  Impure eff lb ub lift next >>= fmb = Impure eff lb ub lift $ CfBind next (Eff . const . fmb)

-- | `CF` is a representation of part of the program's control flow. `CF` is
-- like a continuation function, but because we've listed what's allowed to
-- happen in the continuation, we can inspect and modify it. This allows
-- interpretors to collaborate with each other without knowing anything about
-- each other. It's essential to how Theseus can implement finalizers.
--
-- The most important thing to know about `CF` is that any `CF` must be used
-- linearly. In addition, most of the functions stored within `CF` must also be
-- used linearly if they involve `Eff`s. The only exceptions are the `CfApply`
-- and `CfBind` constructors. The `CF` parameters still must be used linearly,
-- but the others can be used without restrictions.
--
-- Almost no users of Theseus will ever see the CF type. That's because novel
-- control flows are extremely rare. Except for the built in effects, almost
-- all effects will use the `runLinearCf` function to handle a `CF`. This is
-- done internally by all but the `interpretRaw` functions. If an effect wants
-- to throw exceptions or spawn multiple threads, it should almost certainly
-- rely on the existing effects instead of implementing that itself.
data CF input f a where
  -- First the base case. This means there are no control flow operations
  -- happening and that the input is the same as the output.
  CfIn :: CF (f a) f a
  -- These express the Monad family of control flow operations. Theseus is very
  -- unoptomized right now, but one really important optimization is keeping
  -- the `CfFmap` separate from the others. It's easy to end up with a lot of
  -- fmap operations running one after another. We can detect that and turn
  -- them into plain function compositions which GHC optimizes extremely well.
  -- In one realistic benchmark, this changes the amount of memory that has to
  -- be allocated by orders of magnitude.
  CfFmap :: (a -> b) -> CF input f a -> CF input f b
  CfApply :: CF input f (a -> b) -> f a -> CF input f b
  CfBind :: CF input f a -> (a -> f b) -> CF input f b
  -- This runs one of the effects removing it from the stack. The `lb wrap`
  -- constraint says that the type we're changing the result into implements at
  -- least the lower bound. Handlers of `CF` will put requirements on `lb`. For
  -- example, the handler for `Choice` needs to know how to extract the number
  -- of threads from the wrapped type. `Choice` uses a `Traversable` lower
  -- bound for that.
  --
  -- The second parameter is the interpretation of the effect. It MUST be used
  -- linearly. If you don't call it, finalizers will not run. If you call it
  -- too often, finalizers will run too many times. Theseus and Haskell cannot
  -- detect when you make a mistake, so it's up to handler of `CF` to be
  -- careful about this. Luckily there's almost no reason to write your own
  -- `CF` handler, so you can rely on the built in ones to keep the promise.
  CfRun ::
    lb wrap =>
    (forall x. Eff lb ub (e : es) x -> Eff lb ub es (wrap x)) ->
    CF input (Eff lb ub (e : es)) a ->
    CF input (Eff lb ub es) (wrap a)
  -- Almost exactly like `CfRun` except that it interprets an effect that's
  -- anywhere in the stack instead of an effect that's at the top. Theseus
  -- tries to avoid this because it makes reasoning about effects harder. It's
  -- needed for `Choice` because `Choice` has to distribute itself across many
  -- threads. This makes the handler for `Choice` really complicated and
  -- creates awkward edges in the semantics if other effects try to distribute
  -- themselves. Luckily there aren't a lot of good reasons for an effect to
  -- want to distribute itself like `Choice` does. Those that do should
  -- probably just use `Choice` as a private dependency.
  CfInterpose ::
    lb wrap =>
    (forall x. Eff lb ub es x -> Eff lb ub es (wrap x)) ->
    CF input (Eff lb ub es) a ->
    CF input (Eff lb ub es) (wrap a)
  -- These operations manipulate the environment in other common ways. Raising
  -- is helpful when you want to hide an effect from parts of the code.
  -- Unrestricting is how you massage the lower and upper bound constraints.
  -- The bounds can only be widened.
  CfRaise ::
    CF input (Eff lb ub es) a ->
    CF input (Eff lb ub (e : es)) a
  CfRaiseUnder ::
    CF input (Eff lb ub (e : es)) a ->
    CF input (Eff lb ub (e : newE : es)) a
  CfUnrestrict ::
    ubSend `Implies` lbSend ->
    ub `Implies` ubSend ->
    lbSend `Implies` lb ->
    CF input (Eff lbSend ubSend es) a ->
    CF input (Eff lb ub es) a
  -- Remember that every `CF` must be used. A natural thing to try is
  -- ```haskell
  -- run :: CF ... -> Eff lb ub es a
  -- run cf = do
  --  resumeWith <- someAction
  --  runLinearCf resumeWith cf
  -- ```
  -- But that breaks the linearity promise! The do notation will eventually
  -- become `CfBind someAction \_ -> runLineraCf resumeWith cf`. Since there
  -- are no linearity guarantees about how `CfBind`'s second parameter will be
  -- used, that means there's no guarantee that `cf` will be used linearly.
  --
  -- `CfOnce` is how we get around this problem. In specific cases like the one
  -- in the example, we don't need the full generality of `CfBind`. If the `cf`
  -- that we need to use linearly lines up correctly with the operation we want
  -- to perform with its result, we can thread the two together keeping the
  -- linearity promise. Theseus uses this when there are other effects than
  -- need to be sent before resuming the computation.
  CfOnce ::
    lbSend `Implies` lb ->
    Lifter es esSend ->
    CF (Eff lbSend ubSend esSend a) (Eff lb ub es) b ->
    CF input (Eff lb ub es) (Eff lbSend ubSend esSend a) ->
    CF input (Eff lb ub es) b
  -- This exists to solve the same problem as `CfOnce` but in a different case.
  -- Sometimes while handling `CfOnce`, you realize you need to inject your own
  -- `CF` handling code while another handler is running. While I feel like
  -- `CfOnce` behaves reasonably, this one is much more awkward and destroys
  -- information about the running threads. That problem hasn't come up in
  -- practice yet, but I would like to find improvements. The problematic
  -- handlers are in the Choice and Error modules.
  CfPutMeIn ::
    (forall a. Monoid (k a)) =>
    (Eff lbSend ubSend esSend (k a) -> Eff lb ub es (k b)) ->
    CF input (Eff lb ub es) (Eff lbSend ubSend esSend (k a)) ->
    CF input (Eff lb ub es) (k b)

instance Functor f => Functor (CF input f) where
  fmap f (CfFmap f' cf) = CfFmap (f . f') cf
  fmap f cf = CfFmap f cf

-- ## Freer Manipulators

-- This section contains functions that construct and manipulate `freer` values
-- without interpreting them. The interpreters are in a separate module.

-- | This adds a single effect to the computation. You can use the `:>`
-- class to convert an effect into a Union, then using `lift` to convert it
-- into a Freer. The `send` function does all this for you so you probably
-- don't need to call lift manually.
lift :: Union es (Eff lb ub es) a -> Freer lb ub es a
lift f = Impure f idImply idImply Just CfIn

-- | Perform an effect as long as it will be handled somewhere up the stack.
send :: eff :> es => eff (Eff lb ub es) a -> Eff lb ub es a
send eff = Eff $ const $ lift $ inj eff

-- | Adds an extra unused effect onto the top of an effectful computation. This
-- is helpful when you want to hide certain effects from pieces of code. For
-- example, if you specialize it to ``raise :: X :> es => Eff lb ub (X : es)
-- -> Eff lb ub es a``, then any uses of `X` in the input will use the inner
-- interpreter for `X` instead of the outermost one. Any uses of `X` after the
-- `raise` will use the outermost one.
raise :: Eff lb ub es a -> Eff lb ub (eff : es) a
raise (Eff act) = Eff \facts -> case act facts of
  Pure a -> Pure a
  Impure eff lb ub lifter next ->
    Impure
      (raiseUnion eff)
      lb
      ub
      ( \case
          Deeper member -> lifter member
          IsMember _ -> Nothing
      )
      $ CfRaise next
 where
  raiseUnion :: Union es (Eff lb ub esSend) x -> Union (eff : es) (Eff lb ub esSend) x
  raiseUnion (This eff) = That (This eff)
  raiseUnion (That rest) = That $ raiseUnion rest

-- | Like the raise function, but inserts the effect one layer deeper in the
-- stack. This allows you to add private effects to the stack because only the
-- outermost effect can see the raised effects.
raiseUnder :: forall e eff lb ub es a. Eff lb ub (eff : es) a -> Eff lb ub (eff : e : es) a
raiseUnder (Eff act) = Eff \facts -> case act facts of
  Pure a -> pure a
  Impure @_ @_ @_ @esSend eff lb ub lifter next -> Impure (raiseUnderUnion eff) lb ub lifter' $ CfRaiseUnder next
   where
    lifter' :: (forall someEff. someEff `IsMember` (eff : e : es) -> Maybe (someEff `IsMember` esSend))
    lifter' l =
      case l of
        IsMember _ -> lifter getProof
        Deeper (Deeper proof) -> lifter $ Deeper proof
        Deeper (IsMember _) -> Nothing

raiseUnderUnion :: Union (eff : es) (Eff lbSend ubSend esSend) x -> Union (eff : e : es) (Eff lbSend ubSend esSend) x
raiseUnderUnion (This eff) = This eff
raiseUnderUnion (That rest) = That $ That rest

type Lifter es esSend = forall eff. eff `IsMember` es -> Maybe (eff `IsMember` esSend)
