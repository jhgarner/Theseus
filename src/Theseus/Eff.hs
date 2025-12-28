{-# LANGUAGE QuantifiedConstraints #-}

-- Since I'm doing scary things with foralls and constraints, The "use id"
-- HLint only works when DeepSubsumption is turned on. In this module, enabling
-- DeepSubsumption causes a ton of code to stop compiling, so I'm ignoring the
-- lint.
{- HLINT ignore "Use id" -}

module Theseus.Eff (
  Eff (Eff),
  ControlFlow (..),
  Anything,
  Implies (..),
  implying,
  Effect,
  Freer (Pure, Impure),
  unrestrictEff,
  unrestrict,
  lift,
  raise,
  send,
  runEff,
  Member,
  Sender,
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
import Theseus.EffType
import Theseus.Union

type Sender es esSend = (forall e. e `Member` es => (forall y. (e `Member` esSend => y) -> y))

type Handler eff ef es =
  ( forall esSend efSend x a.
    eff (Eff efSend esSend) x ->
    Sender (eff : es) esSend ->
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
    \eff sender next -> fmap Identity $ f eff sender $ handle f . runIdentityCf . next . IdentityCf

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
    \eff sender next -> fmap Identity $ f eff sender $ handleFinally finally f . runIdentityCf . next . IdentityCf

type HandlerWrapped eff ef es wrap =
  ( forall esSend efSend x a.
    eff (Eff efSend esSend) x ->
    Sender (eff : es) esSend ->
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
  handleRaw (pure . wrap) \eff sender next -> f eff sender $ runIdentityCf . next . IdentityCf

type HandlerRaw eff ef es cf wrap =
  ( forall a esSend efSend x.
    eff (Eff efSend esSend) x ->
    Sender (eff : es) esSend ->
    (cf eff (Eff efSend esSend) x -> cf eff (Eff ef (eff : es)) a) ->
    Eff ef es (wrap a)
  )

unrestrictEff :: forall newEf ef es a. (forall a. ef a => newEf a) => Eff ef es a -> Eff newEf es a
unrestrictEff (Eff act) = Eff $ unrestrict act

unrestrict :: forall ef newEf es a. (forall a. ef a => newEf a) => Freer ef es a -> Freer newEf es a
unrestrict (Pure a) = Pure a
unrestrict (Impure eff lift continue) = Impure eff lift \member -> withProof member (cfMap implying unrestrictEff) . continue member

handleRaw ::
  forall a wrap eff ef es outEf cf someEf.
  (outEf wrap, forall w. ef w => outEf w, ControlFlow cf someEf, (forall f. ef f => someEf f)) =>
  (forall x. x -> Eff outEf es (wrap x)) ->
  HandlerRaw eff ef es cf wrap ->
  Eff ef (eff : es) a ->
  Eff outEf es (wrap a)
handleRaw wrap f (Eff act) = case act of
  Pure a -> wrap a
  Impure (This e) lifter next -> unrestrictEff $ f e (liftIt lifter) (next getProof)
  Impure (That rest) lifter next -> Eff $ Impure rest (lifter . Deeper) \member x ->
    withProof member (cfRun implying (handleRaw wrap f)) $ next (Deeper member) x

liftIt :: (forall e. e `IsMember` es -> e `IsMember` esSend) -> (forall e. e `Member` es => (forall y. (e `Member` esSend => y) -> y))
liftIt f = withProof (f $ IsMember \x -> x)

type IHandler eff ef es =
  ( forall esSend efSend x a.
    eff `Member` es =>
    eff (Eff efSend esSend) x ->
    Sender es esSend ->
    (Eff efSend esSend x -> Eff ef es a) ->
    Eff ef es a
  )

interpose :: (eff `Member` es, ef Identity) => IHandler eff ef es -> Eff ef es a -> Eff ef es a
interpose f =
  fmap runIdentity
    . interposeRaw
      pure
      \eff sender continue -> Identity <$> f eff sender (interpose f . runIdentityCf . continue . IdentityCf)

type IHandlerWrapped eff ef es wrap =
  ( forall esSend efSend x a.
    eff `Member` es =>
    eff (Eff efSend esSend) x ->
    Sender es esSend ->
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
    \eff sender continue -> f eff sender (runIdentityCf . continue . IdentityCf)

type IHandlerRaw eff ef es wrap =
  ( forall esSend efSend x a.
    eff `Member` es =>
    eff (Eff efSend esSend) x ->
    Sender es esSend ->
    (forall cf someEf. (ControlFlow cf someEf, forall a. ef a => someEf a) => cf eff (Eff efSend esSend) x -> cf eff (Eff ef es) a) ->
    Eff ef es (wrap a)
  )

interposeRaw ::
  (eff `Member` es, outEf wrap, forall w. ef w => outEf w) =>
  (forall x. x -> wrap x) ->
  IHandlerRaw eff ef es wrap ->
  Eff ef es a ->
  Eff outEf es (wrap a)
interposeRaw ret f (Eff act) = case act of
  Pure a -> pure $ ret a
  Impure union lifter next -> case prj union of
    Just eff -> unrestrictEff $ f eff (liftIt lifter) (next getProof)
    Nothing -> Eff $ Impure union lifter \member ->
      withProof member (cfRun implying (interposeRaw ret f)) . next member

runEff :: Eff Anything '[] a -> a
runEff (Eff act) = case act of
  Pure a -> a
  Impure a _ _ -> case a of {}

newtype IdentityCf eff f a = IdentityCf {runIdentityCf :: f a}
  deriving (Functor)

instance ControlFlow IdentityCf Anything where
  IdentityCf fab `cfApply` fa = IdentityCf $ fab <*> fa
  IdentityCf fa `cfBind` afb = IdentityCf $ fa >>= afb
  cfMap _ efToOut (IdentityCf fa) = IdentityCf $ efToOut fa
  cfRun _ handler (IdentityCf fa) = IdentityCf $ handler fa
