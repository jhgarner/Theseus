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
  interpose',
  runEff,
  runEffDist,
  Member,
  Handler,
  IHandler,
  Boring,
  HandlerWoven,
  handleWoven,
) where

import Control.Monad ((>=>))
import Control.Monad.Identity
import Data.Distributive (Distributive (distribute))
import Data.Kind (Constraint, Type)
import Theseus.Union

newtype Eff (ef :: ExtraFacts) (es :: [Effect]) a = Eff (Freer ef es a)
  deriving (Functor, Applicative, Monad)

type Effect = (Type -> Type) -> Type -> Type

type ExtraFacts = (Type -> Type) -> Constraint

type Freer :: ExtraFacts -> [Effect] -> Type -> Type
data Freer ef es a
  = Pure a
  | forall (efSend :: ExtraFacts) (esSend :: [Effect]) x. Impure
      (Union es (Eff efSend esSend) x)
      (forall g. (ef g, Traversable g, Applicative g) => Eff efSend esSend (g x) -> Eff ef es (g a))

deriving instance Functor (Freer ef es)

instance Applicative (Freer ef es) where
  pure = Pure

  Pure f <*> rhs = fmap f rhs
  Impure eff next <*> m = Impure eff \x -> fmap sequenceA (next x) <*> Eff m

instance Monad (Freer ef es) where
  Pure ma >>= fmb = fmb ma
  -- Impure eff next >>= fmb = Impure eff (next >=> traverse (Eff . fmb))
  Impure eff next >>= fmb = Impure eff \x -> do
    after <- next x
    let rhs = traverse fmb after
    Eff rhs

restrict :: Eff Boring es a -> Eff Distributive es a
restrict (Eff (Pure a)) = Eff $ Pure a
restrict (Eff (Impure eff next)) = Eff $ Impure eff (restrict . next)

lift :: Union es (Eff ef es) a -> Freer ef es a
lift f = Impure f id

raise :: forall eff ef es a. Eff ef es a -> Eff ef (eff : es) a
raise (Eff (Pure a)) = pure a
raise (Eff (Impure eff next)) = Eff $ Impure (raiseEff eff) (raise . next)

raiseEff :: Union es (Eff ef esSend) x -> Union (eff : es) (Eff ef esSend) x
raiseEff (This eff) = That (This eff)
raiseEff (That rest) = That $ raiseEff rest

send :: eff `Member` es => eff (Eff ef es) a -> Eff ef es a
send eff = Eff $ lift $ inj eff

type Handler eff ef es wrap =
  ( forall esSend efSend x a.
    ef Identity =>
    eff (Eff efSend esSend) x ->
    (Eff efSend esSend x -> Eff ef (eff : es) a) ->
    Eff ef es (wrap a)
  )

handle :: (ef Identity, Traversable wrap) => (forall a. a -> Eff ef es (wrap a)) -> Handler eff ef es wrap -> Eff ef (eff : es) a -> Eff ef es (wrap a)
handle ret _ (Eff (Pure a)) = ret a
handle _ f (Eff (Impure (This e) next)) = f e (fmap runIdentity . next . fmap Identity)
handle ret f (Eff (Impure (That rest) next)) = Eff $ Impure rest (fmap sequenceA . handle ret f . next)

type HandlerWoven eff ef es wrap =
  ( forall esSend efSend x a.
    eff (Eff efSend esSend) x ->
    (forall g. (ef g, Traversable g, Applicative g) => Eff efSend esSend (g x) -> Eff ef (eff : es) (g a)) ->
    Eff ef es (wrap a)
  )

handleWoven :: Traversable wrap => (forall a. a -> Eff ef es (wrap a)) -> HandlerWoven eff ef es wrap -> Eff ef (eff : es) a -> Eff ef es (wrap a)
handleWoven ret _ (Eff (Pure a)) = ret a
handleWoven _ f (Eff (Impure (This e) next)) = f e next
handleWoven ret f (Eff (Impure (That rest) next)) = Eff $ Impure rest (fmap sequenceA . handleWoven ret f . next)

type IHandler eff ef es wrap =
  ( forall esSend efSend x a.
    (ef Identity, eff `Member` es) =>
    eff (Eff efSend esSend) x ->
    (Eff efSend esSend x -> Eff ef es a) ->
    Eff ef es (wrap a)
  )

interpose :: (eff `Member` es, Traversable wrap, ef Identity) => (forall a. a -> Eff ef es (wrap a)) -> IHandler eff ef es wrap -> Eff ef es a -> Eff ef es (wrap a)
interpose ret _ (Eff (Pure a)) = ret a
interpose ret f (Eff (Impure union next)) = case prj union of
  Just eff -> f eff (fmap runIdentity . next . fmap Identity)
  Nothing -> Eff (Impure union (fmap sequenceA . interpose ret f . next))

-- interposeWoven :: (eff `Member` es, Traversable wrap) => (forall a. a -> Eff ef es (wrap a)) -> HandlerWoven eff ef es wrap -> Eff ef es a -> Eff ef es (wrap a)
-- interposeWoven ret _ (Eff (Pure a)) = ret a
-- interposeWoven ret f (Eff (Impure union next)) = case prj union of
--   Just eff -> f eff (raise . next)
--   Nothing -> Eff (Impure union (next >=> fmap sequenceA . ret))

handle' :: Functor wrap => (forall a. a -> Eff Distributive es (wrap a)) -> Handler eff Distributive es wrap -> Eff Distributive (eff : es) a -> Eff Distributive es (wrap a)
handle' ret _ (Eff (Pure a)) = ret a
handle' _ f (Eff (Impure (This e) next)) = f e (fmap runIdentity . next . fmap Identity)
handle' ret f (Eff (Impure (That rest) next)) = Eff $ Impure rest (fmap distribute . handle' ret f . next)

interpose' ::
  (eff `Member` es, Functor wrap) =>
  (forall a. a -> Eff Distributive es (wrap a)) ->
  HandlerWoven eff Distributive es wrap ->
  Eff Distributive es a ->
  Eff Distributive es (wrap a)
interpose' ret _ (Eff (Pure a)) = ret a
interpose' ret f (Eff (Impure union next)) = case prj union of
  Just eff -> f eff (raise . next)
  Nothing -> Eff (Impure union (next >=> fmap distribute . ret))

runEff :: Eff Boring '[] a -> a
runEff (Eff (Pure a)) = a
runEff (Eff (Impure a _)) = case a of {}

runEffDist :: Eff Distributive '[] a -> a
runEffDist (Eff (Pure a)) = a
runEffDist (Eff (Impure a _)) = case a of {}

class Boring (f :: Type -> Type)

instance Boring f
