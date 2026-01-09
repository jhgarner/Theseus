{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeFamilyDependencies #-}

module Theseus.Interpreters where

import Control.Monad.Identity
import Data.Bifunctor (Bifunctor (first))
import Theseus.EffType
import Theseus.Union

-- # Interpreting

-- This is where the Eff data type actually does useful work. The EffType
-- helps us understand how Eff is built, and this module helps us understand
-- how Eff is consumed. The most fundamental interpreting function is near the
-- bottom called `interpretRaw`. The others are built on it.
--
-- Theseus also supports "interposing" effects. When you interpose an effect,
-- you replace the handler for one `send` with something else. Interposing is
-- helpful because it can be done on effects regardless of where they are in
-- the stack. Interposing is also kind of hard to use and hides what's going
-- on, so I usually avoid it. You can see in the `Reader` and `Writer` files
-- how Theseus uses standard interpretation instead of interposition.

-- | A Sender is useful when working with higher order effects. It acts a lot
-- like a Quantified Constraint saying that any effects that are in scope for
-- the handler are in scope for the sender. Ideally we'd be able to write it as
-- a real quantified constraint, but I don't think Haskell is expressive enough
-- for that. Instead you need to apply the sender function to whatever needs
-- the constraint. You can think of a `Sender` as removing constraints from
-- values.
type Sender es esSend = (forall e. e `Member` es => (forall y. (e `Member` esSend => y) -> y))

-- | An interpreter for first order effects that use simple control flow and do
-- not change the return type. Almost all effects will use this.
interpret_ ::
  forall eff ef es a.
  ef Identity =>
  Handler_ eff ef es ->
  Eff ef (eff : es) a ->
  Eff ef es a
interpret_ f = interpret (\_ eff -> pure <$> f eff)

type Handler_ eff ef es =
  forall esSend efSend x.
  eff (Eff efSend esSend) x ->
  Eff ef es x

-- | An interpreter for higher order effects that use simple control flow and
-- do not change the return type. Many higher order effects will use this.
interpret ::
  forall eff ef es a.
  ef Identity =>
  Handler eff ef es ->
  Eff ef (eff : es) a ->
  Eff ef es a
interpret f =
  fmap runIdentity . interpretRaw
    (pure . Identity)
    \eff sender next -> do
      continueWith <- f sender eff
      fmap Identity $ interpret f $ runIdentityCf $ next $ IdentityCf continueWith

-- | The output is a computation that the sender can run to continue execution.
type Handler eff ef es =
  forall esSend efSend x.
  Sender (eff : es) esSend ->
  eff (Eff efSend esSend) x ->
  Eff ef es (Eff efSend esSend x)

-- | An interpreter for higher order effects that use simple control flow and
-- change the return type by wrapping the result in something else.
interpretW ::
  forall eff ef es a wrap.
  ef wrap =>
  (forall x. x -> wrap x) ->
  HandlerW eff ef es wrap ->
  Eff ef (eff : es) a ->
  Eff ef es (wrap a)
interpretW wrap f =
  interpretRaw
    (pure . wrap)
    \eff sender next -> do
      (continueWith, handleNext) <- f sender eff
      handleNext $ runIdentityCf $ next $ IdentityCf continueWith

-- | The output of the handler is a value to continue with and a way of
-- interpreting the next effect that's sent. This allows you to keep track of
-- state.
type HandlerW eff ef es wrap =
  forall esSend efSend x a.
  Sender (eff : es) esSend ->
  eff (Eff efSend esSend) x ->
  Eff ef es (Eff efSend esSend x, Eff ef (eff : es) a -> Eff ef es (wrap a))

-- | An interpreter for first order effects that use simple control flow and
-- change the return type by wrapping the result in something else.
interpretW_ ::
  forall eff ef es a wrap.
  ef wrap =>
  (forall x. x -> wrap x) ->
  HandlerW_ eff ef es wrap ->
  Eff ef (eff : es) a ->
  Eff ef es (wrap a)
interpretW_ wrap f = interpretW wrap (\_ eff -> first pure <$> f eff)

type HandlerW_ eff ef es wrap =
  forall esSend efSend x a.
  eff (Eff efSend esSend) x ->
  Eff ef es (x, Eff ef (eff : es) a -> Eff ef es (wrap a))

-- | Proof that `total` is equal to `prefix ++ es`.
class Subset total es where
  -- | This is used by the `using` function to add private effects to the effect
  -- stack. You can use it to do similar things in case `using` isn't flexible
  -- enough.
  raising :: Eff ef (eff : es) a -> Eff ef (eff : total) a

-- Although GHC is fine with subset being the way it is, HLS randomly decides
-- that I need to mark this as Incoherent for some reason. I don't know why.
instance {-# INCOHERENT #-} Subset es es where
  raising = id

instance Subset ls es => Subset (l : ls) es where
  raising act = raiseUnder $ raising act

-- | Add private effects to an interpreter. The effects will be accessible to
-- the current interpreter, but they won't be accessible to anyone else. Use
-- this for "pure" effects that you can never imagine mocking.
--
-- You cannot combine private effects with `sender`. Doing so will trigger
-- a runtime error. This is because the private effect is not in scope for the
-- sender, so there's no way to send it from there.
using ::
  forall eff handlerEs ef es a b.
  Subset handlerEs es =>
  (Eff ef handlerEs a -> Eff ef es b) ->
  (Eff ef (eff : handlerEs) a -> Eff ef handlerEs a) ->
  Eff ef (eff : es) a ->
  Eff ef es b
using deps interpret act = deps $ interpret $ raising act

-- | Moves the effectful operation from the syntactic end of an interpretation
-- to the beginning. For example, `interpret_ (\case -> ...) thing` becomes
-- `with thing $ interpret_ \case ->...`. This is nice because it removes the
-- awkward parentheses around large lambdas.
with :: Eff ef (eff : es) a -> (Eff ef (eff : es) a -> Eff ef es b) -> Eff ef es b
with action interpret = interpret action

-- | Interprets an effect with maximum flexibility. Unless your effect
-- interpretation changes the control flow in strange ways, you probably want
-- one of the other interpreter functions. This one is easier to use
-- incorrectly.
interpretRaw ::
  forall a wrap eff ef es outEf cf someEf.
  (outEf wrap, forall w. ef w => outEf w, ControlFlow cf someEf, (forall f. ef f => someEf f)) =>
  (forall x. x -> Eff outEf es (wrap x)) ->
  -- | The continuation paramter MUST be used linearly. If you call it
  -- multiple times, the semantics will be confusing. If you call it zero
  -- times, finalizers will not run.
  HandlerRaw eff ef es cf wrap ->
  Eff ef (eff : es) a ->
  Eff outEf es (wrap a)
interpretRaw wrap f (Eff act) = case act of
  Pure a -> wrap a
  Impure (This e) lifter next -> unrestrict $ f e (liftIt lifter) (next getProof)
  Impure (That rest) lifter next -> Eff $ Impure rest (lifter . Deeper) \member x ->
    withProof member (cfRun implying (interpretRaw wrap f)) $ next (Deeper member) x

type HandlerRaw eff ef es cf wrap =
  ( forall a esSend efSend x.
    eff (Eff efSend esSend) x ->
    Sender (eff : es) esSend ->
    (cf eff (Eff efSend esSend) x -> cf eff (Eff ef (eff : es)) a) ->
    Eff ef es (wrap a)
  )

-- | Read this as
-- `(IsMember e es -> IsMember e esSend) -> Member e es => Member e esSend`. In
-- other words, it turns a `->` into a `=>`. Of course we can't actually
-- express that in Haskell directly so there's a little extra going on. This is
-- related to the `Sender` and looks vaguely like a quantified constraint.
liftIt :: (forall e. e `IsMember` es -> e `IsMember` esSend) -> (forall e. e `Member` es => (forall y. (e `Member` esSend => y) -> y))
liftIt f = withProof (f getProof)

-- | Allows us to weaken the constraint on Eff. For example, you can turn
-- a Traversable constraint into an Anything constraint. The other direction is
-- not possible.
unrestrict :: forall ef newEf es a. (forall a. ef a => newEf a) => Eff ef es a -> Eff newEf es a
unrestrict (Eff (Pure a)) = Eff $ Pure a
unrestrict (Eff (Impure eff lift continue)) = Eff $ Impure eff lift \member -> withProof member (cfMap implying unrestrict) . continue member

-- | The simplest control flow. It represents a straight line or a single
-- thread.
newtype IdentityCf eff f a = IdentityCf {runIdentityCf :: f a}
  deriving (Functor)

instance ControlFlow IdentityCf Anything where
  IdentityCf fab `cfApply` fa = IdentityCf $ fab <*> fa
  IdentityCf fa `cfBind` afb = IdentityCf $ fa >>= afb
  cfMap _ efToOut (IdentityCf fa) = IdentityCf $ efToOut fa
  cfRun _ handler (IdentityCf fa) = IdentityCf $ handler fa

-- | Replaces one interpretation with another.
interposeRaw ::
  (eff `Member` es, outEf wrap, forall w. ef w => outEf w) =>
  (forall x. x -> wrap x) ->
  IHandlerRaw eff ef es wrap ->
  Eff ef es a ->
  Eff outEf es (wrap a)
interposeRaw ret f (Eff act) = case act of
  Pure a -> pure $ ret a
  Impure union lifter next -> case prj union of
    Just eff -> unrestrict $ f eff (liftIt lifter) (next getProof)
    Nothing -> Eff $ Impure union lifter \member ->
      withProof member (cfRun implying (interposeRaw ret f)) . next member

-- | A handler for an interposition.
type IHandlerRaw eff ef es wrap =
  ( forall esSend efSend x a.
    eff `Member` es =>
    eff (Eff efSend esSend) x ->
    Sender es esSend ->
    (forall cf someEf. (ControlFlow cf someEf, forall a. ef a => someEf a) => cf eff (Eff efSend esSend) x -> cf eff (Eff ef es) a) ->
    Eff ef es (wrap a)
  )
