module Theseus.Effect.Reader (
  Reader (Ask, Local),
  ask,
  local,
  asks,
  runReader,
  DReader (DAsk, DLocal),
  dask,
  dlocal,
  dasks,
  ReadStack,
  runDReader,
) where

import Data.Foldable
import Data.Monoid
import Theseus.Eff
import Theseus.Effect.State

-- # Reader

-- The Reader effect is a good example of a higher order effect because it's
-- otherwise very simple. There are two readers in this module. The first is
-- a lexically scoped reader. The second is a dynamically scoped reader. The
-- first is simpler and more naturally fits into Theseus' architecture. The
-- second is more complicated. Coming from first order effect systems like
-- `freer-simple`, the lexical scoping is what you'd expect. Coming from IO
-- based higher order effect systems like effectful, dynamic scoping is what
-- you'd expect.

-- | Computations that use `Reader r` can ask the environment for some `r`.
-- They cannot change the `r`, but that does not necessarily mean that two
-- calls to `ask` will never return different `r`s. For example, if a call to
-- `yield` happens between the asks, the implementation might be switched out
-- for another. The following laws should hold:
--
-- * `a <- ask; b <- ask; pure (a, b)` === `a <- ask; pure (a, a)`
-- * `local f ask` === `fmap f ask`
data Reader r m a where
  Ask :: Reader r m r
  -- Local is a provider for Readers. It seems like many higher order effects
  -- follow the pattern of being providers for other effects. Sometimes the
  -- provider-ness is hidden behind `interpose`, but it's still there. In
  -- Theseus I'm trying to make that explicit which is why there's a new
  -- `Reader r` constraint on top. Other effect systems (and earlier versions
  -- of Theseus) use `interpose` to hide the new effect. I don't think that's
  -- necessary. The only downside I can see is it makes it possible to skip the
  -- local reader with `raise`. I don't know if that's actually bad though.
  Local :: lb Identity => (r -> r) -> Eff lb ub (Reader r : es) a -> Reader r (Eff lb ub es) a

-- | Returns the `Reader`'s constant value.
ask :: Reader r :> es => Eff lb ub es r
ask = send Ask

-- | Modifies the `Reader`'s value within some limited scope.
local :: lb Identity => Reader r :> es => (r -> r) -> Eff lb ub (Reader r : es) a -> Eff lb ub es a
local f action = send $ Local f action

-- | A convenience function equivalent to `fmap f ask`.
asks :: Reader r :> es => (r -> a) -> Eff lb ub es a
asks f = fmap f ask

-- | Runs a `Reader r` effect with the generally expected semantics.
runReader :: forall r lb ub es a. lb Identity => r -> Eff lb ub (Reader r : es) a -> Eff lb ub es a
runReader r = interpret \sender -> \case
  Ask -> pure $ pure r
  -- Here's an example of `sender` being used so that we can share the `Reader
  -- r` that we're interpreting with the `Local` sender.
  Local f m -> pure $ sender @(Reader r) $ localReader f m

-- | A `runReader` that modifies the result of an inner `Reader r`.
localReader :: forall r lb ub es a. (lb Identity, Reader r :> es) => (r -> r) -> Eff lb ub (Reader r : es) a -> Eff lb ub es a
localReader f = interpret \sender -> \case
  Ask -> pure . f <$> ask
  Local newF m -> pure $ sender @(Reader r) $ localReader (newF . f) m

-- ## Dynamic Reader

-- The default (and simpler) version of Reader is lexically scoped. Code
-- directly inside of a `local` see the modified value, but anything not
-- "syntactically" inside the `local` will not. For example, imagine you wanted
-- to keep track of a stack of locations while logging. For example, you might
-- use some code like `withCtx "doingThing" do action` and any logs emitted within
-- `...` should include the extra context. You might expect the normal `Reader`
-- effect to work for this. If `action = do callDb; log` then it the `log`
-- after `callDb` will work correctly. If `callDb` is an effect and the
-- implementation of `CallDb` calls `log`, it won't see the local context. It
-- would only see the context where `CallDb` is being handled, not the context
-- where `CallDb` is being sent.
--
-- In cases like that one, having a dynamically scoped Reader is extremely
-- helpful. Theseus includes that as a separate `DReader` type

-- | The dynamically scoped Reader has the same laws as `Reader`, but
-- modifications created by `DLocal` are visible within effect interpretations
-- instead of only being visible at the outermost level.
data DReader r m a where
  DAsk :: DReader r m r
  DLocal :: lb Identity => (r -> r) -> Eff lb ub es a -> DReader r (Eff lb ub es) a

-- | Returns the `DReader`'s constant value.
dask :: DReader r :> es => Eff lb ub es r
dask = send DAsk

-- | Modifies the `DReader`'s value within some limited scope.
dlocal :: (lb Identity, DReader r :> es) => (r -> r) -> Eff lb ub es a -> Eff lb ub es a
dlocal f action = send $ DLocal f action

-- | A convenience function equivalent to `fmap f dask`.
dasks :: DReader r :> es => (r -> a) -> Eff lb ub es a
dasks f = fmap f dask

-- The implementation of `DReader` uses `State` to keep track of a stack of
-- local modifications. It looks a lot like the implementation of Readers in IO
-- based effect systems. It relies on Theseus' `finally` function to ensure the
-- stack is modified correctly.

-- | Runs a `DReader r` effect and consumes the `State ReadStack` that it
-- depends on. The `State` is not a private effect because it needs to be
-- sendable by any functions that want to send `DAsk`. That means you should
-- never use raise to hide the `State ReadStack` unless you are also hiding the
-- `DReader` associated with it. Getting this wrong will trigger `error` calls.
--
-- Although it's public, you should not modify the `State ReadStack`. Because
-- `ReadStack` doesn't export its constructor, you shouldn't be able to do much
-- with it anyway.
runDReader ::
  forall r lb ub es a.
  (lb Identity, lb (StateResult (ReadStack r))) =>
  r ->
  Eff lb ub (DReader r : State (ReadStack r) : es) a ->
  Eff lb ub es a
runDReader r =
  evalState mempty . interpret \sender -> \case
    DAsk -> pure . apply r <$> get
    DLocal f m -> do
      modify (push f)
      pure $ sender @(State (ReadStack r)) $ m `finally` modify (pop @r)

-- | An opaque type holding the stack of local modifications.
newtype ReadStack r = ReadStack [Endo r]
  deriving (Semigroup, Monoid)

push :: (r -> r) -> ReadStack r -> ReadStack r
push f (ReadStack rs) = ReadStack (Endo f : rs)

pop :: ReadStack r -> ReadStack r
pop (ReadStack []) = error "The read stack was empty. It might have been replaced with an incompatible one."
pop (ReadStack (_ : rs)) = ReadStack rs

apply :: r -> ReadStack r -> r
apply r (ReadStack rs) = fold rs `appEndo` r
