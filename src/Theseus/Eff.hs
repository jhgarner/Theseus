{-# LANGUAGE QuantifiedConstraints #-}

module Theseus.Eff (
  Eff (Eff),
  ControlFlow (..),
  Boring,
  Implies (..),
  implying,
  Effect,
  -- ExtraFacts,
  Freer (Pure, Impure),
  unrestrictEff,
  unrestrict,
  lift,
  raise,
  send,
  runEff,
  BasicFacts (Facts),
  -- runEffDist,
  Member,
  Handler,
  handle,
  handleFinally,
  HandlerWrapped,
  handleWrapped,
  HandlerRaw,
  handleRaw,
  IHandler,
  interpose,
  IHandlerWrapped,
  interposeWrapped,
  IHandlerRaw,
  interposeRaw,
) where

import Control.Monad.Identity
import Data.Functor
import Theseus.ControlFlow (IdentityCf (IdentityCf, runIdentityCf))
import Theseus.EffType
import Theseus.Union

type Handler eff ef es =
  ( forall esSend efSend x a.
    eff `Member` esSend =>
    eff (Eff efSend esSend) x ->
    (Eff efSend esSend x -> Eff ef es a) ->
    Eff ef es a
  )

handle ::
  forall eff ef es a.
  ef Identity =>
  Handler eff ef es ->
  Eff ef (eff : es) a ->
  Eff ef es a
handle f =
  fmap runIdentity . handleRaw
    (pure . Identity)
    \eff next -> fmap Identity $ f eff $ handle f . runIdentityCf . next . IdentityCf

handleFinally ::
  forall eff ef es a.
  ef Identity =>
  Eff ef es () ->
  Handler eff ef es ->
  Eff ef (eff : es) a ->
  Eff ef es a
handleFinally finally f =
  fmap runIdentity . handleRaw
    (\a -> finally $> Identity a)
    \eff next -> fmap Identity $ f eff $ handleFinally finally f . runIdentityCf . next . IdentityCf

type HandlerWrapped eff ef es wrap =
  ( forall esSend efSend x a.
    eff `Member` esSend =>
    eff (Eff efSend esSend) x ->
    (Eff efSend esSend x -> Eff ef (eff : es) a) ->
    Eff ef es (wrap a)
  )

handleWrapped ::
  ef wrap =>
  (forall x. x -> wrap x) ->
  HandlerWrapped eff ef es wrap ->
  Eff ef (eff : es) a ->
  Eff ef es (wrap a)
handleWrapped @_ wrap f =
  handleRaw (pure . wrap) \eff next -> f eff $ runIdentityCf . next . IdentityCf

type HandlerRaw eff ef es wrap =
  ( forall a esSend efSend x.
    eff `Member` esSend =>
    eff (Eff efSend esSend) x ->
    (forall cf someEf. (ControlFlow cf someEf, forall f. ef f => someEf f) => cf eff (Eff efSend esSend) x -> cf eff (Eff ef (eff : es)) a) ->
    Eff ef es (wrap a)
  )

unrestrictEff :: forall newEf ef es a. (forall a. ef a => newEf a) => Eff ef es a -> Eff newEf es a
unrestrictEff (Eff act) = Eff \Facts -> unrestrict $ act Facts

unrestrict :: forall ef newEf es a. (forall a. ef a => newEf a) => Freer ef es a -> Freer newEf es a
unrestrict (Pure a) = Pure a
unrestrict (Impure eff continue) = Impure eff \member -> withProof member (cfMap implying unrestrictEff) . continue member

handleRaw ::
  forall a wrap eff ef es outEf.
  (outEf wrap, forall w. ef w => outEf w) =>
  (forall x. x -> Eff outEf es (wrap x)) ->
  HandlerRaw eff ef es wrap ->
  Eff ef (eff : es) a ->
  Eff outEf es (wrap a)
handleRaw wrap f (Eff act) = Eff \Facts -> case act Facts of
  Pure a -> unEff (wrap a) Facts
  Impure (This e) next -> unrestrict $ unEff (f e (next getProof)) Facts
  Impure (That rest) next -> Impure rest \member x -> withProof member (cfRun implying (handleRaw wrap f)) $ next (Deeper member) x

type IHandler eff ef es =
  ( forall esSend efSend x a.
    (eff `Member` es, eff `Member` esSend) =>
    eff (Eff efSend esSend) x ->
    (Eff efSend esSend x -> Eff ef es a) ->
    Eff ef es a
  )

interpose :: (eff `Member` es, ef Identity) => IHandler eff ef es -> Eff ef es a -> Eff ef es a
interpose f =
  fmap runIdentity
    . interposeRaw
      pure
      \eff continue -> Identity <$> f eff (interpose f . runIdentityCf . continue . IdentityCf)

type IHandlerWrapped eff ef es wrap =
  ( forall esSend efSend x a.
    (eff `Member` es, eff `Member` esSend) =>
    eff (Eff efSend esSend) x ->
    (Eff efSend esSend x -> Eff ef es a) ->
    Eff ef es (wrap a)
  )

interposeWrapped ::
  (eff `Member` es, ef wrap) =>
  (forall x. x -> wrap x) ->
  IHandlerWrapped eff ef es wrap ->
  Eff ef es a ->
  Eff ef es (wrap a)
interposeWrapped ret f =
  interposeRaw
    ret
    \eff continue -> f eff (runIdentityCf . continue . IdentityCf)

type IHandlerRaw eff ef es wrap =
  ( forall esSend efSend x a.
    (eff `Member` es, eff `Member` esSend) =>
    eff (Eff efSend esSend) x ->
    (forall cf someEf. (ControlFlow cf someEf, forall a. ef a => someEf a) => cf eff (Eff efSend esSend) x -> cf eff (Eff ef es) a) ->
    Eff ef es (wrap a)
  )

interposeRaw ::
  (eff `Member` es, outEf wrap, forall w. ef w => outEf w) =>
  (forall x. x -> wrap x) ->
  IHandlerRaw eff ef es wrap ->
  Eff ef es a ->
  Eff outEf es (wrap a)
interposeRaw ret f (Eff act) = Eff \Facts -> case act Facts of
  Pure a -> unEff (pure $ ret a) Facts
  Impure union next -> case prj union of
    JustFact eff -> unrestrict $ unEff (f eff (next getProof)) Facts
    NothingFact -> Impure union \member -> withProof member (cfRun implying (interposeRaw ret f)) . next member

runEff :: Eff Boring '[] a -> a
runEff (Eff act) = case act Facts of
  Pure a -> a
  Impure a _ -> case a of {}

-- runEffDist :: Eff m '[] a -> a
-- runEffDist (Eff act) = case act Facts of
--   Pure a -> a
--   Impure a _ -> case a of {}
