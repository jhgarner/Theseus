module Theseus.Eff (
  Eff (Eff),
  Effect,
  ExtraFacts,
  Freer (Pure, Impure),
  restrict,
  lift,
  raise,
  send,
  handle,
  interpose,
  handle',
  -- interpose',
  runEff,
  BasicFacts (Facts),
  runEffDist,
  Member,
  Handler,
  IHandler,
  Boring,
  HandlerWoven,
  handleWoven,
) where

import Control.Monad.Identity
import Data.Distributive (Distributive (distribute))
import Data.Kind (Constraint, Type)
import Theseus.Union

data BasicFacts ef where
  Facts :: ef Identity => BasicFacts ef

newtype Eff (ef :: ExtraFacts) (es :: [Effect]) a = Eff {unEff :: BasicFacts ef -> Freer ef es a}
  deriving (Functor)

instance Applicative (Eff ef es) where
  pure a = Eff $ \_ -> pure a
  Eff ma <*> Eff mb = Eff $ \Facts -> ma Facts <*> mb Facts

instance Monad (Eff ef es) where
  Eff ma >>= fmb = Eff $ \Facts -> ma Facts >>= \a -> unEff (fmb a) Facts

type Effect = (Type -> Type) -> Type -> Type

type ExtraFacts = (Type -> Type) -> Constraint

class eff `Member` es => FlipMember es eff
instance eff `Member` es => FlipMember es eff

data Freer :: ExtraFacts -> [Effect] -> Type -> Type where
  Pure :: a -> Freer ef es a
  Impure ::
    efSend Identity =>
    (Union es (FlipMember esSend) (Eff efSend esSend) x) ->
    (forall g. (ef g, Traversable g, Applicative g) => Eff efSend esSend (g x) -> Eff ef es (g a)) ->
    Freer ef es a

deriving instance Functor (Freer ef es)

instance Applicative (Freer ef es) where
  pure = Pure

  Pure f <*> rhs = fmap f rhs
  Impure eff next <*> m = Impure eff \x -> fmap sequenceA (next x) <*> Eff (const m)

instance Monad (Freer ef es) where
  Pure ma >>= fmb = fmb ma
  -- Impure eff next >>= fmb = Impure eff (next >=> traverse (Eff . fmb))
  Impure eff next >>= fmb = Impure eff \x -> do
    after <- next x
    let rhs = traverse fmb after
    Eff $ const rhs

restrict :: Eff Boring es a -> Eff Distributive es a
restrict (Eff act) = Eff \Facts -> case act Facts of
  Pure a -> Pure a
  Impure eff next -> Impure eff (restrict . next)

lift :: ef Identity => Union es (FlipMember es) (Eff ef es) a -> Freer ef es a
lift f = Impure f id

raise :: forall eff ef es a. Eff ef es a -> Eff ef (eff : es) a
raise (Eff act) = Eff \Facts -> case act Facts of
  Pure a -> pure a
  Impure eff next -> Impure (raiseEff eff) (raise . next)

raiseEff :: Union es (FlipMember esSend) (Eff ef esSend) x -> Union (eff : es) (FlipMember esSend) (Eff ef esSend) x
raiseEff (This eff) = That (This eff)
raiseEff (That rest) = That $ raiseEff rest

send :: eff `Member` es => eff (Eff ef es) a -> Eff ef es a
send eff = Eff \Facts -> lift $ inj eff

type Handler eff ef es wrap =
  ( forall esSend efSend x a.
    (ef Identity, efSend Identity, eff `Member` esSend) =>
    eff (Eff efSend esSend) x ->
    (Eff efSend esSend x -> Eff ef (eff : es) a) ->
    Eff ef es (wrap a)
  )

handle :: Traversable wrap => (forall a. a -> Eff ef es (wrap a)) -> Handler eff ef es wrap -> Eff ef (eff : es) a -> Eff ef es (wrap a)
handle ret f (Eff act) = Eff $ \Facts -> case act Facts of
  Pure a -> unEff (ret a) Facts
  Impure (This e) next -> unEff (f e (fmap runIdentity . next . fmap Identity)) Facts
  Impure (That rest) next -> Impure rest (fmap sequenceA . handle ret f . next)

type HandlerWoven eff ef es wrap =
  ( forall esSend efSend x a.
    (ef Identity, efSend Identity, eff `Member` esSend) =>
    eff (Eff efSend esSend) x ->
    (forall g. (ef g, Traversable g, Applicative g) => Eff efSend esSend (g x) -> Eff ef (eff : es) (g a)) ->
    Eff ef es (wrap a)
  )

handleWoven :: Traversable wrap => (forall a. a -> Eff ef es (wrap a)) -> HandlerWoven eff ef es wrap -> Eff ef (eff : es) a -> Eff ef es (wrap a)
-- handleWoven ret _ (Eff (Pure a)) = ret a
-- handleWoven _ f (Eff (Impure (This e) next)) = f e next
handleWoven ret f (Eff act) = Eff $ \Facts -> case act Facts of
  Pure a -> unEff (ret a) Facts
  Impure (This e) next -> unEff (f e next) Facts
  Impure (That rest) next -> Impure rest (fmap sequenceA . handleWoven ret f . next)

type IHandler eff ef es wrap =
  ( forall esSend efSend x a.
    (ef Identity, efSend Identity, eff `Member` es, eff `Member` esSend) =>
    eff (Eff efSend esSend) x ->
    (Eff efSend esSend x -> Eff ef es a) ->
    Eff ef es (wrap a)
  )

interpose :: (eff `Member` es, Traversable wrap) => (forall a. a -> Eff ef es (wrap a)) -> IHandler eff ef es wrap -> Eff ef es a -> Eff ef es (wrap a)
interpose ret f (Eff act) = Eff \Facts -> case act Facts of
  Pure a -> unEff (ret a) Facts
  Impure union next -> case prj union of
    JustFact eff -> unEff (f eff (fmap runIdentity . next . fmap Identity)) Facts
    NothingFact -> Impure union (fmap sequenceA . interpose ret f . next)

-- interposeWoven :: (eff `Member` es, Traversable wrap) => (forall a. a -> Eff ef es (wrap a)) -> HandlerWoven eff ef es wrap -> Eff ef es a -> Eff ef es (wrap a)
-- interposeWoven ret _ (Eff (Pure a)) = ret a
-- interposeWoven ret f (Eff (Impure union next)) = case prj union of
--   Just eff -> f eff (raise . next)
--   Nothing -> Eff (Impure union (next >=> fmap sequenceA . ret))

handle' :: Functor wrap => (forall a. a -> Eff Distributive es (wrap a)) -> Handler eff Distributive es wrap -> Eff Distributive (eff : es) a -> Eff Distributive es (wrap a)
handle' ret f (Eff act) = Eff \Facts -> case act Facts of
  Pure a -> unEff (ret a) Facts
  Impure (This e) next -> unEff (f e (fmap runIdentity . next . fmap Identity)) Facts
  Impure (That rest) next -> Impure rest (fmap distribute . handle' ret f . next)

-- interpose' ::
--   (eff `Member` es, Functor wrap) =>
--   (forall a. a -> Eff Distributive es (wrap a)) ->
--   HandlerWoven eff Distributive es wrap ->
--   Eff Distributive es a ->
--   Eff Distributive es (wrap a)
-- interpose' ret _ (Eff (Pure a)) = ret a
-- interpose' ret f (Eff (Impure union next)) = case prj union of
--   Just eff -> f eff (raise . next)
--   Nothing -> Eff (Impure union (next >=> fmap distribute . ret))

runEff :: Eff Boring '[] a -> a
runEff (Eff act) = case act Facts of
  Pure a -> a
  Impure a _ -> case a of {}

runEffDist :: Eff Distributive '[] a -> a
runEffDist (Eff act) = case act Facts of
  Pure a -> a
  Impure a _ -> case a of {}

class Boring (f :: Type -> Type)

instance Boring f
