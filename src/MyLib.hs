{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module MyLib (
  Eff (Eff),
  Freer (..),
  Union (..),
  Boring,
  inj,
  runEff,
  runEffIO,
  raise,
  runReader,
  ask,
  local,
  asks,
  State (Get, Put),
  evalState,
  execState,
  runState,
  get,
  put,
  gets,
  Catch (Catch),
  Throw (Throw),
  catch,
  throw,
  runCatch,
  runThrow,
  runCatchNoRecovery,
  NonDet,
  runNonDet,
  Coroutine (Yield),
  runCoroutine,
  expectCoroutine,
  Status (Done, Yielded),
  yield,
  ValidExtraFacts,
  handle,
  interpose,
  handle',
  interpose',
  runEffDist,
  restrict,
) where

import Control.Monad.IO.Class (MonadIO (liftIO))
import Data.Kind

-- import Control.Monad.IO.Unlift (MonadUnliftIO (withRunInIO))

import Control.Applicative (Alternative (empty, (<|>)))
import Control.Monad (join, (>=>))
import Control.Monad.Identity
import Data.Distributive (Distributive, distribute)
import Data.Functor

-- import GHC.Generics (Generic, Generic1)

class ValidExtraFacts (c :: ExtraFacts)

instance ValidExtraFacts c

-- default ValidExtraFacts (Boring)

class Boring (f :: Type -> Type)

instance Boring f

class (a f, b f) => And (a :: ExtraFacts) (b :: ExtraFacts) (f :: Type -> Type)

instance (a f, b f) => And a b f

type Effect = (Type -> Type) -> Type -> Type

type ExtraFacts = (Type -> Type) -> Constraint

type Freer :: ExtraFacts -> [Effect] -> Type -> Type
data Freer ef es a
  = Pure a
  | forall (efSend :: ExtraFacts) (esSend :: [Effect]) x. Impure
      (Union es efSend esSend x)
      (forall g. (ef g, Traversable g, Applicative g) => Eff efSend esSend (g x) -> Eff ef es (g a))

deriving instance Functor (Freer ef es)

instance Applicative (Freer ef es) where
  pure = Pure

  Pure f <*> rhs = fmap f rhs
  Impure eff next <*> m = Impure eff \x -> do
    after <- next x
    rhs <- fmap pure (Eff m)
    pure $ after <*> rhs

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

lift :: Union es ef es a -> Freer ef es a
lift f = Impure f id

raise :: Eff ef es a -> Eff ef (eff : es) a
raise (Eff (Pure a)) = pure a
raise (Eff (Impure eff next)) = Eff $ Impure (raiseEff eff) (raise . next)

raiseEff :: Union es ef esSend x -> Union (eff : es) ef esSend x
raiseEff (This eff) = That (This eff)
raiseEff (That rest) = That $ raiseEff rest

data Union (ls :: [Effect]) (ef :: ExtraFacts) (es :: [Effect]) (a :: Type) where
  This :: eff (Eff ef es) a -> Union (eff : ls) ef es a
  That :: Union ls ef es a -> Union (eff : ls) ef es a

data Reader r m a where
  Ask :: Reader r m r
  Local :: (Reader r `Member` es, ef Identity) => (r -> r) -> Eff ef es a -> Reader r (Eff ef es) a

ask :: Reader r `Member` es => Eff ef es r
ask = send Ask

asks :: Reader r `Member` es => (r -> a) -> Eff ef es a
asks = (<$> ask)

local :: (Reader r `Member` es, ef Identity) => (r -> r) -> Eff ef es a -> Eff ef es a
local f = send . Local f

runReader :: ef Identity => r -> Eff ef (Reader r : es) a -> Eff ef es a
runReader r = fmap runIdentity . handle (pure . pure) (elabReader r)

elabReader :: ef Identity => r -> Handler (Reader r) ef es Identity
elabReader r Ask next = fmap Identity $ runReader r $ fmap runIdentity $ next $ pure $ pure r
elabReader r (Local f m) next = Identity <$> runReader r (runIdentity <$> next (interpose (pure . pure) (elabReader $ f r) m))

data State s m a where
  Get :: State s m s
  Put :: s -> State s m ()

get :: State s `Member` es => Eff ef es s
get = send Get

gets :: State s `Member` es => (s -> a) -> Eff ef es a
gets = (<$> send Get)

put :: State s `Member` es => s -> Eff ef es ()
put = send . Put

runState :: ef Identity => s -> Eff ef (State s : es) a -> Eff ef es (s, a)
runState s = handle (pure . (s,)) $ elabState s

elabState :: ef Identity => s -> Handler (State s) ef es ((,) s)
elabState s Get next = runState s $ fmap runIdentity $ next $ pure $ pure s
elabState _ (Put s') next = runState s' $ fmap runIdentity $ next $ pure $ pure ()

execState :: ef Identity => s -> Eff ef (State s : es) a -> Eff ef es s
execState s = fmap fst . runState s

evalState :: ef Identity => s -> Eff ef (State s : es) a -> Eff ef es a
evalState s = fmap snd . runState s

newtype Throw e m a where
  Throw :: e -> Throw e m a

throw :: Throw e `Member` es => e -> Eff ef es a
throw = send . Throw

data Catch m a where
  Catch :: Eff ef (Throw e : es) a -> (e -> Eff ef es a) -> Catch (Eff ef es) a

catch :: Catch `Member` es => Eff ef (Throw e : es) a -> (e -> Eff ef es a) -> Eff ef es a
catch action onThrow = send $ Catch action onThrow

runCatch :: ef Identity => Eff ef (Catch : es) a -> Eff ef es a
runCatch = fmap runIdentity . handle (pure . pure) elabCatch

elabCatch :: ef Identity => Handler Catch ef es Identity
elabCatch (Catch action onThrow) next = fmap Identity $ runCatch $ fmap runIdentity $ next $ fmap pure $ runThrow action >>= either onThrow pure

runThrow :: Eff ef (Throw e : es) a -> Eff ef es (Either e a)
runThrow = handle (pure . pure) elabThrow

elabThrow :: Handler (Throw e) ef es (Either e)
elabThrow (Throw e) _ = pure $ Left e

runCatchNoRecovery :: ef Maybe => Eff ef (Catch : es) a -> Eff ef es (Maybe a)
runCatchNoRecovery = handle (pure . Just) elabCatchNoRecovery

elabCatchNoRecovery :: ef Maybe => Handler Catch ef es Maybe
elabCatchNoRecovery (Catch action _) next = do
  ran <- runCatchNoRecovery $ next $ runThrowNoRecovery action
  pure $ join ran

runThrowNoRecovery :: Eff ef (Throw e : es) a -> Eff ef es (Maybe a)
runThrowNoRecovery = handle (pure . Just) elabThrowNoRecovery

elabThrowNoRecovery :: Handler (Throw e) ef es Maybe
elabThrowNoRecovery (Throw _) _ = pure Nothing

data NonDet m a where
  Empty :: NonDet m a
  (:<|>) :: m a -> m a -> NonDet m a

runNonDet ::
  (ef Identity, LazyAlternative f, Traversable f) =>
  Eff ef (NonDet : es) a ->
  Eff ef es (f a)
runNonDet = handle (pure . pure) elabNonDet

elabNonDet ::
  (ef Identity, LazyAlternative f, Traversable f) =>
  Handler NonDet ef es f
elabNonDet Empty _ = pure empty
elabNonDet (lhs :<|> rhs) next =
  runNonDet (fmap runIdentity $ next $ fmap pure lhs) `lazyAlt` runNonDet (fmap runIdentity $ next $ fmap pure rhs)

class Alternative f => LazyAlternative f where
  lazyAlt :: Monad g => g (f a) -> g (f a) -> g (f a)

instance LazyAlternative [] where
  lazyAlt = liftA2 (<|>)

instance LazyAlternative Maybe where
  lazyAlt ga gb = ga >>= maybe gb (pure . Just)

instance NonDet `Member` es => Alternative (Eff ef es) where
  empty = send Empty
  a <|> b = send $ a :<|> b

data Coroutine a b m c where
  Yield :: a -> Coroutine a b m b

yield :: forall a2 a1 ef es. Coroutine a1 a2 `Member` es => a1 -> Eff ef es a2
yield a = send $ Yield a

data Status es a b c = Done c | Yielded a (b -> Eff Distributive (Coroutine a b : es) c)
  deriving (Functor)

runCoroutine :: Eff Distributive (Coroutine a b : es) c -> Eff Distributive es (Status es a b c)
runCoroutine = handle' (pure . Done) elabCoroutine

elabCoroutine :: Handler (Coroutine a b) Distributive es (Status es a b)
elabCoroutine (Yield a) next = pure $ Yielded a (fmap runIdentity . next . pure . Identity)

expectCoroutine :: Eff Distributive (Coroutine a b : es) c -> Eff Distributive es (Maybe c)
expectCoroutine action =
  runCoroutine action <&> \case
    Done c -> Just c
    Yielded _ _ -> Nothing

-- data Delay m a where
--   Delay :: Eff es a -> Delay (Eff es) ()
--
-- runDelay :: Eff (Delay : es) a -> Eff es a
-- runDelay = handle pure elabDelay
--
-- elabDelay :: Handler Delay es a a
-- elabDelay (Delay action) next = runDelay $ next (pure ()) >> action

class InternalMember eff ls where
  internalInj :: eff (Eff ef es) a -> Union ls ef es a
  internalPrj :: Union ls ef es a -> Maybe (eff (Eff ef es) a)

instance InternalMember eff (eff : es) where
  internalInj = This

  internalPrj (This eff) = Just eff
  internalPrj (That _) = Nothing

instance {-# OVERLAPPABLE #-} InternalMember eff es => InternalMember eff (other : es) where
  internalInj eff = That $ internalInj eff

  internalPrj (This _) = Nothing
  internalPrj (That rest) = internalPrj rest

class InternalMember eff es => Member eff es where
  inj :: eff (Eff ef es) a -> Union es ef es a

prj :: InternalMember eff ls => Union ls ef es a -> Maybe (eff (Eff ef es) a)
prj = internalPrj

instance InternalMember eff es => Member eff es where
  inj = internalInj

newtype Eff (ef :: ExtraFacts) (es :: [Effect]) a = Eff (Freer ef es a)
  deriving (Functor, Applicative, Monad)

send :: eff `Member` es => eff (Eff ef es) a -> Eff ef es a
send eff = Eff $ lift $ inj eff

type Handler eff ef es wrap =
  ( forall esSend efSend x a.
    eff (Eff efSend esSend) x ->
    (forall g. (ef g, Traversable g, Applicative g) => Eff efSend esSend (g x) -> Eff ef (eff : es) (g a)) ->
    Eff ef es (wrap a)
  )

handle :: Traversable wrap => (forall a. a -> Eff ef es (wrap a)) -> Handler eff ef es wrap -> Eff ef (eff : es) a -> Eff ef es (wrap a)
handle ret _ (Eff (Pure a)) = ret a
handle _ f (Eff (Impure (This e) next)) = f e next
handle ret f (Eff (Impure (That rest) next)) = Eff $ Impure rest (fmap sequenceA . handle ret f . next)

interpose :: (eff `Member` es, Traversable wrap) => (forall a. a -> Eff ef es (wrap a)) -> Handler eff ef es wrap -> Eff ef es a -> Eff ef es (wrap a)
interpose ret _ (Eff (Pure a)) = ret a
interpose ret f (Eff (Impure union next)) = case prj union of
  Just eff -> f eff (raise . next)
  Nothing -> Eff (Impure union (next >=> fmap sequenceA . ret))

handle' :: Functor wrap => (forall a. a -> Eff Distributive es (wrap a)) -> Handler eff Distributive es wrap -> Eff Distributive (eff : es) a -> Eff Distributive es (wrap a)
handle' ret _ (Eff (Pure a)) = ret a
handle' _ f (Eff (Impure (This e) next)) = f e next
handle' ret f (Eff (Impure (That rest) next)) = Eff $ Impure rest (fmap distribute . handle' ret f . next)

interpose' ::
  (eff `Member` es, Functor wrap) =>
  (forall a. a -> Eff Distributive es (wrap a)) ->
  Handler eff Distributive es wrap ->
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

data EIO m a where
  LiftIO :: IO a -> EIO m a

-- UnliftIO :: ((forall a. m a -> IO a) -> IO b) -> EIO m b

runEffIO :: Eff Boring '[EIO] a -> IO a
runEffIO (Eff (Pure a)) = pure a
runEffIO (Eff (Impure (This (LiftIO io)) next)) = io >>= runEffIO . fmap runIdentity . next . pure . pure
runEffIO (Eff (Impure (That union) _)) = case union of {}

instance EIO `Member` es => MonadIO (Eff ef es) where
  liftIO = send . LiftIO

-- instance Free c (Eff es)

-- instance EIO `Member` es => MonadUnliftIO (Eff es) where
--   withRunInIO action = send $ UnliftIO action
