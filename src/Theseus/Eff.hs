{-# LANGUAGE QuantifiedConstraints #-}

-- Since I'm doing scary things with foralls and constraints, The "use id"
-- HLint only works when DeepSubsumption is turned on. In this module, enabling
-- DeepSubsumption causes a ton of code to stop compiling, so I'm ignoring the
-- lint.
{- HLINT ignore "Use id" -}

module Theseus.Eff (
  -- * Effects

  -- | Theseus is an effect system library for Haskell. You define effects
  -- locally using GADT syntax. For example,
  -- @
  --  data Terminal
  -- @
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
  raiseUnder,
  Subset (raising),
  send,
  runEff,
  Member,
  using,
  with,
  Sender,
  Handler,
  interpret,
  Handler_,
  interpret_,
  HandlerW,
  interpretW,
  HandlerW_,
  interpretW_,
  HandlerRaw,
  interpretRaw,
  IHandler,
  interpose,
  IHandlerWrapped,
  interposeWrapped,
  IHandlerRaw,
  interposeRaw,
  Identity,
) where

import Control.Monad.Identity
import Theseus.EffType
import Theseus.Interpreters
import Theseus.Union

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
