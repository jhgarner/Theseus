{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE ImpredicativeTypes #-}

module Theseus.Interpreters where

import Control.Monad.Identity
import Data.Bifunctor (Bifunctor (first))
import Data.Maybe
import Theseus.Constraints
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
type Sender es esSend = (forall e. e :> es => (forall y. (e :> esSend => y) -> y))

-- | An interpreter for first order effects that use simple control flow and do
-- not change the return type. Almost all effects will use this.
interpret_ ::
  forall eff lb ub es a.
  lb Identity =>
  Handler_ eff lb ub es ->
  Eff lb ub (eff : es) a ->
  Eff lb ub es a
interpret_ f = interpret (\_ eff -> pure <$> f eff)

type Handler_ eff lb ub es =
  forall esSend lbSend ubSend x.
  eff (Eff lbSend ubSend esSend) x ->
  Eff lb ub es x

-- | An interpreter for higher order effects that use simple control flow and
-- do not change the return type. Many higher order effects will use this.
interpret ::
  forall eff lb ub es a.
  lb Identity =>
  Handler eff lb ub es ->
  Eff lb ub (eff : es) a ->
  Eff lb ub es a
interpret @eff f =
  fmap runIdentity . interpretRaw
    isoSomeId
    (pure . Identity)
    \eff lb _ lifter next ->
      matchOn (f (sendIt lifter) eff) >>= \case
        Pure a -> fmap Identity $ interpret f $ runIdentityCf $ evalCf implying (Just getProof) next $ IdentityCf @eff a
        Impure eff lb' ub' lifter' next' ->
          Eff $
            const $
              Impure eff lb' ub' lifter' $
                CfOnce
                  lb
                  (lifter . Deeper)
                  (\implies member' cf -> cfRun member' (fmap Identity . interpret f) $ evalCf implies (fmap Deeper member') next cf)
                  next'

-- | The output is a computation that the sender can run to continue execution.
type Handler eff lb ub es =
  forall esSend lbSend ubSend x.
  Sender (eff : es) esSend ->
  eff (Eff lbSend ubSend esSend) x ->
  Eff lb ub es (Eff lbSend ubSend esSend x)

-- | An interpreter for higher order effects that use simple control flow and
-- change the return type by wrapping the result in something else.
interpretW ::
  forall eff lb ub es a wrap.
  lb wrap =>
  (forall x. x -> Eff lb ub es (wrap x)) ->
  HandlerW eff lb ub es wrap ->
  Eff lb ub (eff : es) a ->
  Eff lb ub es (wrap a)
interpretW wrap f =
  interpretRaw
    isoSomeId
    wrap
    \eff lb _ lifter next -> Eff \facts -> do
      case first (effUn facts) $ f (sendIt lifter) eff of
        (Pure a, continue) -> effUn facts $ continue $ runIdentityCf $ evalCf implying (Just getProof) next $ IdentityCf @eff a
        (Impure eff lb' ub' lifter' next', continue) ->
          Impure eff lb' ub' lifter' $
            CfOnce lb (lifter . Deeper) (\implying member' cf -> cfRun member' continue $ evalCf implying (fmap Deeper member') next cf) next'

-- | The output of the handler is a value to continue with and a way of
-- interpreting the next effect that's sent. This allows you to keep track of
-- state.
type HandlerW eff lb ub es wrap =
  forall esSend lbSend ubSend x.
  Sender (eff : es) esSend ->
  eff (Eff lbSend ubSend esSend) x ->
  (Eff lb ub es (Eff lbSend ubSend esSend x), forall a. Eff lb ub (eff : es) a -> Eff lb ub es (wrap a))

-- | An interpreter for first order effects that use simple control flow and
-- change the return type by wrapping the result in something else.
interpretW_ ::
  forall eff lb ub es a wrap.
  lb wrap =>
  (forall x. x -> Eff lb ub es (wrap x)) ->
  HandlerW_ eff lb ub es wrap ->
  Eff lb ub (eff : es) a ->
  Eff lb ub es (wrap a)
interpretW_ wrap f = interpretW wrap (\_ eff -> first (fmap pure) $ f eff)

type HandlerW_ eff lb ub es wrap =
  forall esSend lbSend ubSend x.
  eff (Eff lbSend ubSend esSend) x ->
  (Eff lb ub es x, forall a. Eff lb ub (eff : es) a -> Eff lb ub es (wrap a))

-- | Proof that `total` is equal to `prefix ++ es`.
class Subset total es where
  -- | This is used by the `using` function to add private effects to the effect
  -- stack. You can use it to do similar things in case `using` isn't flexible
  -- enough.
  raising :: Eff lb ub (eff : es) a -> Eff lb ub (eff : total) a

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
  forall eff handlerEs lb ub es a b.
  Subset handlerEs es =>
  (Eff lb ub handlerEs a -> Eff lb ub es b) ->
  (Eff lb ub (eff : handlerEs) a -> Eff lb ub handlerEs a) ->
  Eff lb ub (eff : es) a ->
  Eff lb ub es b
using deps interpret act = deps $ interpret $ raising act

-- | Moves the effectful operation from the syntactic end of an interpretation
-- to the beginning. For example, `interpret_ (\case -> ...) thing` becomes
-- `with thing $ interpret_ \case ->...`. This is nice because it removes the
-- awkward parentheses around large lambdas.
with :: Eff lb ub es' a -> (Eff lb ub es' a -> Eff lb ub es b) -> Eff lb ub es b
with action interpret = interpret action

data VoidEffect :: Effect

-- | Guarantees that the first parameter will run exactly once as soon as the
-- second parameter is complete. This applies even if the second parameter uses
-- effects that manipulate the control flow.
finally :: lb Identity => Eff lb ub es a -> Eff lb ub es () -> Eff lb ub es a
finally (Eff act) final = Eff \facts -> case act facts of
  Pure a -> effUn facts $ final >> pure a
  Impure eff lb ub lifter next ->
    Impure eff lb ub lifter $
      runIdentity <$> CfInterpose (fmap Identity . flip finally final) next

-- | Interprets an effect with maximum flexibility. Unless your effect
-- interpretation changes the control flow in strange ways, you probably want
-- one of the other interpreter functions. This one is easier to use
-- incorrectly.
interpretRaw ::
  forall a wrap eff lb ub es.
  wrap `IsoSome` lb ->
  (forall x. x -> Eff lb ub es (wrap x)) ->
  -- | The continuation paramter MUST be used linearly. If you call it
  -- multiple times, the semantics will be confusing. If you call it zero
  -- times, finalizers will not run.
  HandlerRaw eff lb ub es wrap ->
  Eff lb ub (eff : es) a ->
  Eff lb ub es (wrap a)
interpretRaw iso@(IsoSome (Iso fromWrap toWrap)) wrap f (Eff act) = Eff \facts -> case act facts of
  Pure a -> unEff (wrap a) facts
  Impure (This e) lb ub lifter next -> unEff (f e lb ub lifter next) facts
  Impure (That rest) lb ub lifter next ->
    fmap toWrap $
      Impure rest lb ub (lifter . Deeper) $
        CfRun (fmap fromWrap . interpretRaw iso wrap f) next

type HandlerRaw eff lb ub es wrap =
  ( forall a esSend lbSend ubSend x.
    eff (Eff lbSend ubSend esSend) x ->
    lbSend `Implies` lb ->
    ub `Implies` ubSend ->
    Lifter (eff : es) esSend ->
    CF (Eff lbSend ubSend esSend x) (Eff lb ub (eff : es)) a ->
    Eff lb ub es (wrap a)
  )

-- | Read this as
-- `(IsMember e es -> IsMember e esSend) -> Member e es => Member e esSend`. In
-- other words, it turns a `->` into a `=>`. Of course we can't actually
-- express that in Haskell directly so there's a little extra going on. This is
-- related to the `Sender` and looks vaguely like a quantified constraint.
sendIt :: (forall e. e `IsMember` es -> Maybe (e `IsMember` esSend)) -> (forall e. e :> es => (forall y. (e :> esSend => y) -> y))
sendIt f = withProof (fromMaybe (error "Attempted to send a private effect dependency") $ f getProof)

-- | Allows us to weaken the constraint on Eff. For example, you can turn
-- a Traversable constraint into an Anything constraint. The other direction is
-- not possible.
unrestrict ::
  forall lbSend ubSend lb ub es a.
  (lbSend `IsAtLeast` lb, ub `IsAtLeast` ubSend) =>
  ubSend `Implies` lbSend ->
  Eff lbSend ubSend es a ->
  Eff lb ub es a
unrestrict boundedSend (Eff act) = Eff \_ -> case act $ Facts boundedSend of
  Pure a -> Pure a
  Impure eff lb ub lift continue ->
    Impure eff (transImply lb implyAtLeast) (transImply implyAtLeast ub) lift $
      CfUnrestrict boundedSend implyAtLeast implyAtLeast continue

unrestrict' ::
  forall lbSend ubSend lb ub es a.
  ubSend `Implies` lbSend ->
  ub `Implies` ubSend ->
  lbSend `Implies` lb ->
  Eff lbSend ubSend es a ->
  Eff lb ub es a
unrestrict' boundedSend ub' lb' (Eff act) = Eff \_ -> case act $ Facts boundedSend of
  Pure a -> Pure a
  Impure eff lb ub lift continue ->
    Impure eff (transImply lb lb') (transImply ub' ub) lift $
      CfUnrestrict boundedSend ub' lb' continue

-- | The simplest control flow. It represents a straight line or a single
-- thread.
newtype IdentityCf eff f a = IdentityCf {runIdentityCf :: f a}
  deriving (Functor)

instance ControlFlow IdentityCf Anything where
  IdentityCf fab `cfApply` fa = IdentityCf $ fab <*> fa
  IdentityCf fa `cfBind` afb = IdentityCf $ fa >>= afb
  cfOnce ogLb member lifter handler (IdentityCf @eff fea) = IdentityCf do
    matchOn fea >>= \case
      Pure a -> runIdentityCf $ handler implying member $ IdentityCf @eff a
      Impure eff lb ub lifter' next -> Eff \_ ->
        Impure eff lb ub lifter' $
          CfOnce ogLb lifter handler next
  cfPutMeIn _ f (IdentityCf fka) = IdentityCf do
    matchOn fka >>= \case
      Pure a -> f a
      Impure eff lb ub lifter next -> Eff \_ ->
        Impure eff lb ub lifter $ CfPutMeIn f next
  cfRaise (IdentityCf fa) = IdentityCf $ raise fa
  cfRaiseUnder (IdentityCf fa) = IdentityCf $ raiseUnder fa
  cfUnrestrict _ bounded ub lb (IdentityCf fa) = IdentityCf $ unrestrict' bounded ub lb fa
  cfRun _ handler (IdentityCf fa) = IdentityCf $ handler fa

-- | Replaces one interpretation with another.
interposeRaw ::
  (eff :> es, lb wrap, ControlFlow cf r) =>
  lb `Implies` r ->
  (forall x. x -> wrap x) ->
  IHandlerRaw eff lb ub es cf wrap ->
  Eff lb ub es a ->
  Eff lb ub es (wrap a)
interposeRaw topImply ret f (Eff act) = Eff \facts -> case act facts of
  Pure a -> pure $ ret a
  Impure union lb ub lifter next -> case prj union of
    Just eff -> effUn facts $ f eff lb ub (sendIt lifter) (evalCf topImply (Just getProof) next)
    Nothing ->
      Impure union lb ub lifter $ CfInterpose (interposeRaw topImply ret f) next

-- | A handler for an interposition.
type IHandlerRaw eff lb ub es cf wrap =
  ( forall esSend lbSend ubSend x a.
    eff :> es =>
    eff (Eff lbSend ubSend esSend) x ->
    lbSend `Implies` lb ->
    ub `Implies` ubSend ->
    Sender es esSend ->
    (cf eff (Eff lbSend ubSend esSend) x -> cf eff (Eff lb ub es) a) ->
    Eff lb ub es (wrap a)
  )

-- ## Finish Interpreting an Eff

-- | Finishes running an Eff. If your Eff used IO, look in the IO module for
-- the runEffIO function instead. Depending on what other effects you've run,
-- you might need to use `unrestrict` so that the first parameter contains the
-- right constraint.
runEff :: Eff Anything Nonthing '[] a -> a
runEff (Eff act) = case act (Facts implying) of
  Pure a -> a
  Impure a _ _ _ _ -> case a of {}

-- | Lifts a Monad into an Effect. This will likely be the last thing in your
-- effect list.
data Final m f a where
  Final :: m a -> Final m f a

-- | Finishes running an Eff by translating it into some Monad `m`. You must be
-- careful about how `m` changes control flow. The `fmap` implementation on your
-- `m` should call the function passed exactly once. The IO module handles the
-- common case for the `IO` type by getting rid of Exceptions.
runEffM :: Monad m => Eff Anything Nonthing '[Final m] a -> m a
runEffM @m =
  runEff . interpretRaw isoSomeId (pure . pure) \(Final ma) _ _ _ next ->
    pure $ runEffM =<< getComposeCf (evalCf implying (Just getProof) next $ ComposeCf @m @(Final m) $ fmap pure ma)

newtype ComposeCf f eff g a = ComposeCf {getComposeCf :: f (g a)}
  deriving (Functor)

instance Functor m => ControlFlow (ComposeCf m) Anything where
  ComposeCf mfab `cfApply` fa = ComposeCf $ fmap (<*> fa) mfab
  ComposeCf mfa `cfBind` afb = ComposeCf $ fmap (>>= afb) mfa
  cfOnce ogLb member lifter handler (ComposeCf @_ @eff cf) = ComposeCf do
    thing <- cf
    pure do
      matchOn thing >>= \case
        Pure a -> runIdentityCf $ handler implying member $ IdentityCf @eff a
        Impure eff lb ub lifter' next -> Eff \_ ->
          Impure eff lb ub lifter' $ CfOnce ogLb lifter handler next
  cfPutMeIn _ f (ComposeCf @_ cf) = ComposeCf do
    thing <- cf
    pure do
      matchOn thing >>= \case
        Pure a -> f a
        Impure eff lb ub lifter next -> Eff \_ ->
          Impure eff lb ub lifter $ CfPutMeIn f next

  cfRaise (ComposeCf mfa) = ComposeCf $ fmap raise mfa
  cfRaiseUnder (ComposeCf mfa) = ComposeCf $ fmap raiseUnder mfa
  cfUnrestrict _ bounded ub lb (ComposeCf mfa) = ComposeCf $ fmap (unrestrict' bounded ub lb) mfa
  cfRun _ handler (ComposeCf mfa) = ComposeCf $ fmap handler mfa
