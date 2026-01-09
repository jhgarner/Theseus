{-# LANGUAGE QuantifiedConstraints #-}

module Theseus.Effect.Error where

import Control.Monad (join)
import Control.Monad.Identity
import Data.Functor
import Theseus.Eff

-- # Error

-- Error is a good example of something with complicated control flow.

-- | We separate out the Throw and Catch effects so that you can more easily
-- scope when throwing an exception is allowed.
newtype Throw e m a where
  Throw :: e -> Throw e m a

throw :: Throw e `Member` es => e -> Eff ef es a
throw e = send $ Throw e

-- | This is a provider for `Throw` effects.
data Catch m a where
  Catch :: ef (Either e) => Eff ef (Throw e : es) a -> (e -> Eff ef es a) -> Catch (Eff ef es) a

catch :: (Catch `Member` es, ef (Either e)) => Eff ef (Throw e : es) a -> (e -> Eff ef es a) -> Eff ef es a
catch action onThrow = send $ Catch action onThrow

runCatch :: ef Identity => Eff ef (Catch : es) a -> Eff ef es a
runCatch = interpret \_ (Catch action onThrow) ->
  pure $ runThrow action >>= either onThrow pure

-- | A control flow data type which ignores any attempts to continue the
-- control flow. Instead it keeps track of the value that was thrown and
-- a series of finalizers to run.
data Thrown e eff f a = Thrown {getThrown :: e, finalizers :: f ()}
  deriving (Functor)

finishThrown :: Functor f => Thrown e eff f a -> f e
finishThrown (Thrown e finalizers) = finalizers $> e

instance ControlFlow (Thrown e) Anything where
  -- Note how it ignores the rhs of these operations. It acts a lot like Const.
  Thrown e f `cfApply` _ = Thrown e f
  Thrown e f `cfBind` _ = Thrown e f
  cfMap _ handler (Thrown e f) = Thrown e $ handler f

  -- Note that we don't ignore the handler. This is because `cfRun` requires
  -- that the `handler` parameter be used linearly.
  cfRun _ handler (Thrown e f) = Thrown e $ handler f $> ()

runThrow :: forall e ef es a. ef (Either e) => Eff ef (Throw e : es) a -> Eff ef es (Either e a)
-- Although Throw is first order, it modifies the control flow, so we have to
-- use `interpretRaw`.
runThrow = interpretRaw (pure . pure) \(Throw e) _ next ->
  -- We run the `next` function that was passed into our interpreter. Most
  -- other effect systems would simply ignore the continuation. Theseus doesn't
  -- ignore the continuation because we want finalizers to run.
  --
  -- Originally the `runThrow` function didn't have any of the finalizer stuff
  -- and Theseus didn't have the linearity constraints. After adding those,
  -- I had to add the `takeError` function call. That seemed weird, but really
  -- it's the same problem most languages with try-finally blocks have: what do
  -- you do when the finalizer throws an exception? Anyway, I think it's cool
  -- that the type system forces us to confront problems like this that are
  -- shared with non-functional non-statically typed languages. Since the
  -- solutions are shared, the solutions can also be shared. Just like how Java
  -- added the `suppressed` field to its exception types so that the original
  -- exception wouldn't be lost, we could do something similar. For now we just
  -- ignore the original exception.
  fmap takeError $ runThrow $ finishThrown $ next $ Thrown e (pure ())

takeError :: Either e e -> Either e a
takeError = either Left Left

-- | Like `runCatch` except it completely ignores the catching block. If
-- anything throws, the entire computation finishes with `Nothing`.
runCatchNoRecovery :: (ef Maybe, forall w. Traversable w => ef w) => Eff Traversable (Catch : es) a -> Eff ef es (Maybe a)
runCatchNoRecovery = interpretRaw (pure . pure) \(Catch action _) _ next -> do
  ran <- runCatchNoRecovery $ runMaybeCf $ next $ MaybeCf $ either (const Nothing) Just <$> runThrow action
  pure $ join ran

newtype MaybeCf eff f a = MaybeCf {runMaybeCf :: f (Maybe a)}
  deriving (Functor)

-- This is an example of a control flow that uses Traversable. Why do Control
-- Flows ever need `Traversable` or really anything more strict than
-- `Anything`? The interpreter's scope is separate from the sender's scope.
-- Getting information from the interpreter to the sender is easy, but passing
-- information in the opposite direction is harder. You can only get
-- information out of the sender and into the interpreter by running the
-- continuation, which means running all the other effects that were added to
-- the stack after the current interpreter. Some of those other interpreters
-- might want to change the type of the return value. Now we have a problem.
-- Our current interpreter wants to thread some information through the
-- continuation's output, but the continuation might wrap the output in
-- arbitrary other things. The `Traversable` constraint ensures that we can
-- extract the extra information from the wrapped output.
--
-- A `Traversable` constraint isn't the only way to handle this. If the
-- information we wanted to pass around were `Distributive`, we would only need
-- `Functor`. We could also go stricter and require that our threaded
-- information be never duplicated or lost by requiring some kind of
-- `LinearTraversable` or `AffineTraversable`. The former would would remove
-- the `Applicative` constraint from the `traverse` function, and the latter
-- would only require a `Pure` typeclass. There's also probably something fun
-- to do with `Comonad` to say that it's OK to duplicate or drop the wrapper.
-- That also seems to related to linearity. We could argue that
-- `data StateOutput s a = SO s a` is not a `Comonad` because duplicating or
-- dropping the state leads to strange semantics. That would prevent certain
-- effect orderings at compile time. We could have an `UnliftIO` effect which
-- requires `Comonad` which would conveniently line up with the usual UnliftIO
-- restrictions. Anyway, at this point I'm probably confusing things, but
-- I think it's an interesting direction to study.
instance ControlFlow MaybeCf Traversable where
  MaybeCf fmab `cfApply` fa = MaybeCf $ (\mab a -> fmap ($ a) mab) <$> fmab <*> fa
  MaybeCf fma `cfBind` afb = MaybeCf $ fma >>= traverse afb
  cfMap _ efToOut (MaybeCf fa) = MaybeCf $ efToOut fa
  cfRun _ handler (MaybeCf fa) = MaybeCf $ sequenceA <$> handler fa
