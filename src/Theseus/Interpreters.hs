{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeFamilyDependencies #-}

module Theseus.Interpreters where

import Control.Monad.Identity
import Data.Bifunctor (Bifunctor (first))
import Theseus.EffType
import Theseus.Union

type Sender es esSend = (forall e. e `Member` es => (forall y. (e `Member` esSend => y) -> y))
type Interpreter eff ef es wrap a = Eff ef (eff : es) a -> Eff ef es (wrap a)

type HandlerRaw eff ef es cf wrap =
  ( forall a esSend efSend x.
    eff (Eff efSend esSend) x ->
    Sender (eff : es) esSend ->
    (cf eff (Eff efSend esSend) x -> cf eff (Eff ef (eff : es)) a) ->
    Eff ef es (wrap a)
  )

type Handler eff ef es =
  forall esSend efSend x.
  Sender (eff : es) esSend ->
  eff (Eff efSend esSend) x ->
  Eff ef es (Eff efSend esSend x)

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

type Handler_ eff ef es =
  forall esSend efSend x.
  eff (Eff efSend esSend) x ->
  Eff ef es x

interpret_ ::
  forall eff ef es a.
  ef Identity =>
  Handler_ eff ef es ->
  Eff ef (eff : es) a ->
  Eff ef es a
interpret_ f = interpret (\_ eff -> pure <$> f eff)

type HandlerW eff ef es wrap =
  forall esSend efSend x a.
  Sender (eff : es) esSend ->
  eff (Eff efSend esSend) x ->
  Eff ef es (Eff efSend esSend x, Eff ef (eff : es) a -> Eff ef es (wrap a))

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

type HandlerW_ eff ef es wrap =
  forall esSend efSend x a.
  eff (Eff efSend esSend) x ->
  Eff ef es (x, Eff ef (eff : es) a -> Eff ef es (wrap a))

interpretW_ ::
  forall eff ef es a wrap.
  ef wrap =>
  (forall x. x -> wrap x) ->
  HandlerW_ eff ef es wrap ->
  Eff ef (eff : es) a ->
  Eff ef es (wrap a)
interpretW_ wrap f = interpretW wrap (\_ eff -> first pure <$> f eff)

class Subset total es where
  raising :: Eff ef (eff : es) a -> Eff ef (eff : total) a

-- Although GHC is fine with subset being the way it is, HLS randomly decides
-- that I need to mark this as Incoherent for some reason. I don't know why.
instance {-# INCOHERENT #-} Subset es es where
  raising = id

instance Subset ls es => Subset (l : ls) es where
  raising act = raiseUnder $ raising act

using ::
  forall eff handlerEs ef es a b.
  Subset handlerEs es =>
  (Eff ef handlerEs a -> Eff ef es b) ->
  (Eff ef (eff : handlerEs) a -> Eff ef handlerEs a) ->
  Eff ef (eff : es) a ->
  Eff ef es b
using deps interpret act = deps $ interpret $ raising act

with :: Eff ef (eff : es) a -> (Eff ef (eff : es) a -> Eff ef es b) -> Eff ef es b
with action interpret = interpret action

interpretRaw ::
  forall a wrap eff ef es outEf cf someEf.
  (outEf wrap, forall w. ef w => outEf w, ControlFlow cf someEf, (forall f. ef f => someEf f)) =>
  (forall x. x -> Eff outEf es (wrap x)) ->
  HandlerRaw eff ef es cf wrap ->
  Eff ef (eff : es) a ->
  Eff outEf es (wrap a)
interpretRaw wrap f (Eff act) = case act of
  Pure a -> wrap a
  Impure (This e) lifter next -> unrestrictEff $ f e (liftIt lifter) (next getProof)
  Impure (That rest) lifter next -> Eff $ Impure rest (lifter . Deeper) \member x ->
    withProof member (cfRun implying (interpretRaw wrap f)) $ next (Deeper member) x

liftIt :: (forall e. e `IsMember` es -> e `IsMember` esSend) -> (forall e. e `Member` es => (forall y. (e `Member` esSend => y) -> y))
liftIt f = withProof (f getProof)

unrestrictEff :: forall newEf ef es a. (forall a. ef a => newEf a) => Eff ef es a -> Eff newEf es a
unrestrictEff (Eff act) = Eff $ unrestrict act

unrestrict :: forall ef newEf es a. (forall a. ef a => newEf a) => Freer ef es a -> Freer newEf es a
unrestrict (Pure a) = Pure a
unrestrict (Impure eff lift continue) = Impure eff lift \member -> withProof member (cfMap implying unrestrictEff) . continue member

newtype IdentityCf eff f a = IdentityCf {runIdentityCf :: f a}
  deriving (Functor)

instance ControlFlow IdentityCf Anything where
  IdentityCf fab `cfApply` fa = IdentityCf $ fab <*> fa
  IdentityCf fa `cfBind` afb = IdentityCf $ fa >>= afb
  cfMap _ efToOut (IdentityCf fa) = IdentityCf $ efToOut fa
  cfRun _ handler (IdentityCf fa) = IdentityCf $ handler fa
