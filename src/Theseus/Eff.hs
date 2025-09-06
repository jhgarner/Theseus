module Theseus.Eff (
  Eff (Eff),
  Effect,
  ExtraFacts,
  Freer (Pure, Impure),
  restrict,
  lift,
  raise,
  raiseUnder,
  send,
  interpose,
  runEff,
  BasicFacts (Facts),
  runEffDist,
  Member,
  Handler,
  handle,
  HandlerWrapped,
  handleWrapped,
  HandlerRaw,
  handleRaw,
  IHandler,
  IHandlerWrapped,
  interposeWrapped,
  IHandlerRaw,
  interposeRaw,
  Boring,
) where

import Control.Monad.Identity
import Control.Monad.Reader (ReaderT (ReaderT))
import Data.Distributive (Distributive)
import Data.Kind (Constraint, Type)
import Theseus.Union

newtype Eff (ef :: ExtraFacts) (es :: [Effect]) a = Eff {unEff :: BasicFacts ef -> Freer ef es a}
  deriving (Functor)
  deriving (Applicative, Monad) via (ReaderT (BasicFacts ef) (Freer ef es))

-- Things about the ef variable on Eff that must be true in order for Eff to be
-- runnable. We can construct an Eff where these are false, but we won't be able
-- to run it.
data BasicFacts ef where
  Facts :: ef Identity => BasicFacts ef

type Effect = (Type -> Type) -> Type -> Type

type ExtraFacts = (Type -> Type) -> Constraint

class eff `Member` es => FlipMember es eff
instance eff `Member` es => FlipMember es eff

data Freer :: ExtraFacts -> [Effect] -> Type -> Type where
  Pure :: a -> Freer ef es a
  Impure ::
    efSend Identity =>
    (Union es (FlipMember esSend) (Eff efSend esSend) x) ->
    -- TODO Traversable is required for Freer to be a Monad. Either Traversable
    -- or Applicative is required for Freer to be Applicative. I wonder if I can
    -- do something interesting with that. Are there interesting Applicatives I
    -- might want to use as `g` which would allow parallelizable computations?
    -- It would be nice to remove Applicative in cases where I want to pass
    -- `Const` as `g`. That helps you implement effects that aren't scoped.
    (forall g. (ef g, Traversable g, Applicative g) => Eff efSend esSend (g x) -> Eff ef es (g a)) ->
    Freer ef es a

deriving instance Functor (Freer ef es)

instance Applicative (Freer ef es) where
  pure = Pure

  Pure f <*> rhs = fmap f rhs
  Impure eff next <*> m = Impure eff \x -> fmap sequenceA (next x) <*> Eff (const m)

instance Monad (Freer ef es) where
  Pure ma >>= fmb = fmb ma
  Impure eff next >>= fmb = Impure eff \x -> do
    after <- next x
    let rhs = traverse fmb after
    Eff $ const rhs

-- TODO I'd like this to be more generic and have a really easy way of
-- controlling which constraints you requer. That type of type level programming
-- is a rabbit hole I didn't want to jump into yet.
restrict :: Eff Boring es a -> Eff Distributive es a
restrict (Eff act) = Eff \Facts -> case act Facts of
  Pure a -> Pure a
  Impure eff next -> Impure eff (restrict . next)

lift :: ef Identity => Union es (FlipMember es) (Eff ef es) a -> Freer ef es a
lift f = Impure f id

raise :: forall eff ef es a. Eff ef es a -> Eff ef (eff : es) a
raise (Eff act) = Eff \Facts -> case act Facts of
  Pure a -> pure a
  Impure eff next -> Impure (raiseUnion eff) (raise . next)

raiseUnion :: Union es (FlipMember esSend) (Eff ef esSend) x -> Union (eff : es) (FlipMember esSend) (Eff ef esSend) x
raiseUnion (This eff) = That (This eff)
raiseUnion (That rest) = That $ raiseUnion rest

raiseUnder :: forall eff2 eff1 ef es a. Eff ef (eff1 : es) a -> Eff ef (eff1 : eff2 : es) a
raiseUnder (Eff act) = Eff \Facts -> case act Facts of
  Pure a -> pure a
  Impure eff next -> Impure (raiseUnionUnder eff) (raiseUnder . next)

raiseUnionUnder :: Union (eff1 : es) (FlipMember esSend) (Eff ef esSend) x -> Union (eff1 : eff2 : es) (FlipMember esSend) (Eff ef esSend) x
raiseUnionUnder (This eff) = This eff
raiseUnionUnder (That rest) = That $ raiseUnion rest

send :: eff `Member` es => eff (Eff ef es) a -> Eff ef es a
send eff = Eff \Facts -> lift $ inj eff

type Handler eff ef es =
  ( forall esSend efSend x a.
    (ef Identity, efSend Identity, eff `Member` esSend) =>
    eff (Eff efSend esSend) x ->
    (Eff efSend esSend x -> Eff ef es a) ->
    Eff ef es a
  )

distId :: Functor g => Identity (g a) -> g (Identity a)
distId (Identity ga) = fmap Identity ga

handle ::
  forall eff ef es a.
  Handler eff ef es ->
  Eff ef (eff : es) a ->
  Eff ef es a
handle f =
  fmap runIdentity . handleRaw
    (fmap distId)
    (pure . Identity)
    \eff next -> fmap Identity $ f eff $ handle f . fmap runIdentity . next . fmap Identity

type HandlerWrapped eff ef es wrap =
  ( forall esSend efSend x a.
    (ef Identity, efSend Identity, eff `Member` esSend) =>
    eff (Eff efSend esSend) x ->
    (Eff efSend esSend x -> Eff ef (eff : es) a) ->
    Eff ef es (wrap a)
  )

handleWrapped ::
  (forall a g. (ef g, Traversable g, Applicative g) => wrap (g a) -> g (wrap a)) ->
  (forall a. a -> wrap a) ->
  HandlerWrapped eff ef es wrap ->
  Eff ef (eff : es) a ->
  Eff ef es (wrap a)
handleWrapped threading ret f =
  handleRaw
    (fmap threading)
    (pure . ret)
    \eff next -> f eff $ fmap runIdentity . next . fmap Identity

type HandlerRaw eff ef es wrap =
  ( forall a esSend efSend x.
    (ef Identity, efSend Identity, eff `Member` esSend) =>
    eff (Eff efSend esSend) x ->
    (forall g. (ef g, Traversable g, Applicative g) => Eff efSend esSend (g x) -> Eff ef (eff : es) (g a)) ->
    Eff ef es (wrap a)
  )

handleRaw ::
  forall a wrap eff ef es.
  (forall g a. (ef g, Traversable g, Applicative g) => Eff ef es (wrap (g a)) -> Eff ef es (g (wrap a))) ->
  (forall a. a -> Eff ef es (wrap a)) ->
  HandlerRaw eff ef es wrap ->
  Eff ef (eff : es) a ->
  Eff ef es (wrap a)
handleRaw threading ret f (Eff act) = Eff $ \Facts -> case act Facts of
  Pure a -> unEff (ret a) Facts
  Impure (This e) next -> unEff (f e next) Facts
  Impure (That rest) next -> Impure rest $ threading . handleRaw threading ret f . next

type IHandler eff ef es =
  ( forall esSend efSend x a.
    (ef Identity, efSend Identity, eff `Member` es, eff `Member` esSend) =>
    eff (Eff efSend esSend) x ->
    (Eff efSend esSend x -> Eff ef es a) ->
    Eff ef es a
  )

interpose :: eff `Member` es => IHandler eff ef es -> Eff ef es a -> Eff ef es a
interpose f =
  fmap runIdentity
    . interposeRaw
      (fmap distId)
      (pure . Identity)
      \eff continue -> Identity <$> f eff (interpose f . fmap runIdentity . continue . fmap Identity)

type IHandlerWrapped eff ef es wrap =
  ( forall esSend efSend x a.
    (ef Identity, efSend Identity, eff `Member` es, eff `Member` esSend) =>
    eff (Eff efSend esSend) x ->
    (Eff efSend esSend x -> Eff ef es a) ->
    Eff ef es (wrap a)
  )

interposeWrapped ::
  eff `Member` es =>
  (forall g a. (ef g, Traversable g, Applicative g) => wrap (g a) -> g (wrap a)) ->
  (forall a. a -> wrap a) ->
  IHandlerWrapped eff ef es wrap ->
  Eff ef es a ->
  Eff ef es (wrap a)
interposeWrapped threading ret f =
  interposeRaw
    (fmap threading)
    (pure . ret)
    \eff continue -> f eff (fmap runIdentity . continue . fmap Identity)

type IHandlerRaw eff ef es wrap =
  ( forall esSend efSend x a.
    (ef Identity, efSend Identity, eff `Member` es, eff `Member` esSend) =>
    eff (Eff efSend esSend) x ->
    (forall g. (ef g, Traversable g, Applicative g) => Eff efSend esSend (g x) -> Eff ef es (g a)) ->
    Eff ef es (wrap a)
  )

interposeRaw ::
  eff `Member` es =>
  (forall g a. (ef g, Traversable g, Applicative g) => Eff ef es (wrap (g a)) -> Eff ef es (g (wrap a))) ->
  (forall a. a -> Eff ef es (wrap a)) ->
  IHandlerRaw eff ef es wrap ->
  Eff ef es a ->
  Eff ef es (wrap a)
interposeRaw threading ret f (Eff act) = Eff \Facts -> case act Facts of
  Pure a -> unEff (ret a) Facts
  Impure union next -> case prj union of
    JustFact eff -> unEff (f eff next) Facts
    NothingFact -> Impure union (threading . interposeRaw threading ret f . next)

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
