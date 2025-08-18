{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}

module MyLib (
  Eff (Eff),
  Freer (..),
  Union (..),
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
) where

import Control.Monad.IO.Class (MonadIO (liftIO))
import Data.Kind

-- import Control.Monad.IO.Unlift (MonadUnliftIO (withRunInIO))

import Control.Applicative (Alternative (empty, (<|>)))
import Control.Monad (join, (>=>))
import Control.Monad.Identity
import GHC.Generics (Generic, Generic1)

type Effect = (Type -> Type) -> Type -> Type

type Freer :: [Effect] -> Type -> Type
data Freer es a
  = Pure a
  | forall (esSend :: [Effect]) x. Impure
      (Union es esSend x)
      (forall g. (Traversable g, Applicative g) => Eff esSend (g x) -> Eff es (g a))

deriving instance Functor (Freer h)

instance Applicative (Freer es) where
  pure = Pure

  Pure f <*> rhs = fmap f rhs
  Impure eff next <*> m = Impure eff \x -> do
    after <- next x
    rhs <- fmap pure (Eff m)
    pure $ after <*> rhs

instance Monad (Freer f) where
  Pure ma >>= fmb = fmb ma
  -- Impure eff next >>= fmb = Impure eff (next >=> traverse (Eff . fmb))
  Impure eff next >>= fmb = Impure eff \x -> do
    after <- next x
    let rhs = traverse fmb after
    Eff rhs

lift :: Union es es a -> Freer es a
lift f = Impure f id

raise :: Eff es a -> Eff (eff : es) a
raise (Eff (Pure a)) = pure a
raise (Eff (Impure eff next)) = Eff $ Impure (raiseEff eff) (raise . next)

raiseEff :: Union es esSend x -> Union (eff : es) esSend x
raiseEff (This eff) = That (This eff)
raiseEff (That rest) = That $ raiseEff rest

data Union (ls :: [Effect]) (es :: [Effect]) (a :: Type) where
  This :: eff (Eff es) a -> Union (eff : ls) es a
  That :: Union ls es a -> Union (eff : ls) es a

data Reader r m a where
  Ask :: Reader r m r
  Local :: Reader r `Member` es => (r -> r) -> Eff es a -> Reader r (Eff es) a

ask :: Reader r `Member` es => Eff es r
ask = send Ask

asks :: Reader r `Member` es => (r -> a) -> Eff es a
asks = (<$> ask)

local :: Reader r `Member` es => (r -> r) -> Eff es a -> Eff es a
local f = send . Local f

runReader :: r -> Eff (Reader r : es) a -> Eff es a
runReader r = fmap runIdentity . handle (pure . pure) (elabReader r)

elabReader :: r -> Handler (Reader r) es Identity
elabReader r Ask next = fmap Identity $ runReader r $ fmap runIdentity $ next $ pure $ pure r
elabReader r (Local f m) next = Identity <$> runReader r (runIdentity <$> next (interpose (pure . pure) (elabReader $ f r) m))

data State s m a where
  Get :: State s m s
  Put :: s -> State s m ()

get :: State s `Member` es => Eff es s
get = send Get

gets :: State s `Member` es => (s -> a) -> Eff es a
gets = (<$> send Get)

put :: State s `Member` es => s -> Eff es ()
put = send . Put

runState :: s -> Eff (State s : es) a -> Eff es (s, a)
runState s = handle (pure . (s,)) $ elabState s

elabState :: s -> Handler (State s) es ((,) s)
elabState s Get next = runState s $ fmap runIdentity $ next $ pure $ pure s
elabState _ (Put s') next = runState s' $ fmap runIdentity $ next $ pure $ pure ()

execState :: s -> Eff (State s : es) a -> Eff es s
execState s = fmap fst . runState s

evalState :: s -> Eff (State s : es) a -> Eff es a
evalState s = fmap snd . runState s

newtype Throw e m a where
  Throw :: e -> Throw e m a

throw :: Throw e `Member` es => e -> Eff es a
throw = send . Throw

data Catch m a where
  Catch :: Eff (Throw e : es) a -> (e -> Eff es a) -> Catch (Eff es) a

catch :: Catch `Member` es => Eff (Throw e : es) a -> (e -> Eff es a) -> Eff es a
catch action onThrow = send $ Catch action onThrow

runCatch :: Eff (Catch : es) a -> Eff es a
runCatch = fmap runIdentity . handle (pure . pure) elabCatch

elabCatch :: Handler Catch es Identity
elabCatch (Catch action onThrow) next = fmap Identity $ runCatch $ fmap runIdentity $ next $ fmap pure $ runThrow action >>= either onThrow pure

runThrow :: Eff (Throw e : es) a -> Eff es (Either e a)
runThrow = handle (pure . pure) elabThrow

elabThrow :: Handler (Throw e) es (Either e)
elabThrow (Throw e) _ = pure $ Left e

runCatchNoRecovery :: Eff (Catch : es) a -> Eff es (Maybe a)
runCatchNoRecovery = handle (pure . Just) elabCatchNoRecovery

elabCatchNoRecovery :: Handler Catch es Maybe
elabCatchNoRecovery (Catch action _) next = do
  ran <- runCatchNoRecovery $ next $ runThrowNoRecovery action
  pure $ join ran

runThrowNoRecovery :: Eff (Throw e : es) a -> Eff es (Maybe a)
runThrowNoRecovery = handle (pure . Just) elabThrowNoRecovery

elabThrowNoRecovery :: Handler (Throw e) es Maybe
elabThrowNoRecovery (Throw _) _ = pure Nothing

data NonDet m a where
  Empty :: NonDet m a
  (:<|>) :: m a -> m a -> NonDet m a

runNonDet ::
  (LazyAlternative f, Traversable f) =>
  Eff (NonDet : es) a ->
  Eff es (f a)
runNonDet = handle (pure . pure) elabNonDet

elabNonDet ::
  (LazyAlternative f, Traversable f) =>
  Handler NonDet es f
elabNonDet Empty _ = pure empty
elabNonDet (lhs :<|> rhs) next =
  runNonDet (fmap runIdentity $ next $ fmap pure lhs) `lazyAlt` runNonDet (fmap runIdentity $ next $ fmap pure rhs)

class Alternative f => LazyAlternative f where
  lazyAlt :: Monad g => g (f a) -> g (f a) -> g (f a)

instance LazyAlternative [] where
  lazyAlt = liftA2 (<|>)

instance LazyAlternative Maybe where
  lazyAlt ga gb = ga >>= maybe gb (pure . Just)

instance NonDet `Member` es => Alternative (Eff es) where
  empty = send Empty
  a <|> b = send $ a :<|> b

data Coroutine a b m c where
  Yield :: a -> Coroutine a b m b

yield :: Coroutine a1 a2 `Member` es => a1 -> Eff es a2
yield a = send $ Yield a

data Status es a b c = Done c | Yielded a (b -> Eff (Coroutine a b : es) c)
  deriving (Functor, Generic, Generic1)

runCoroutine :: Eff (Coroutine a b : es) c -> Eff es (Status es a b c)
runCoroutine = handle (pure . Done) elabCoroutine

elabCoroutine :: Handler (Coroutine a b) es (Status es a b)
elabCoroutine (Yield a) next = undefined

-- data Delay m a where
--   Delay :: Eff es a -> Delay (Eff es) ()
--
-- runDelay :: Eff (Delay : es) a -> Eff es a
-- runDelay = handle pure elabDelay
--
-- elabDelay :: Handler Delay es a a
-- elabDelay (Delay action) next = runDelay $ next (pure ()) >> action

class InternalMember eff ls where
  internalInj :: eff (Eff es) a -> Union ls es a
  internalPrj :: Union ls es a -> Maybe (eff (Eff es) a)

instance InternalMember eff (eff : es) where
  internalInj = This

  internalPrj (This eff) = Just eff
  internalPrj (That _) = Nothing

instance {-# OVERLAPPABLE #-} InternalMember eff es => InternalMember eff (other : es) where
  internalInj eff = That $ internalInj eff

  internalPrj (This _) = Nothing
  internalPrj (That rest) = internalPrj rest

class InternalMember eff es => Member eff es where
  inj :: eff (Eff es) a -> Union es es a

prj :: InternalMember eff ls => Union ls es a -> Maybe (eff (Eff es) a)
prj = internalPrj

instance InternalMember eff es => Member eff es where
  inj = internalInj

newtype Eff (es :: [Effect]) a = Eff (Freer es a)
  deriving (Functor, Applicative, Monad)

send :: eff `Member` es => eff (Eff es) a -> Eff es a
send eff = Eff $ lift $ inj eff

type Handler eff es wrap =
  ( forall esSend x a.
    eff (Eff esSend) x ->
    (forall g. (Traversable g, Applicative g) => Eff esSend (g x) -> Eff (eff : es) (g a)) ->
    Eff es (wrap a)
  )

handle :: Traversable wrap => (forall a. a -> Eff es (wrap a)) -> Handler eff es wrap -> Eff (eff : es) a -> Eff es (wrap a)
handle ret _ (Eff (Pure a)) = ret a
handle _ f (Eff (Impure (This e) next)) = f e next
handle ret f (Eff (Impure (That rest) next)) = Eff $ Impure rest (fmap sequenceA . handle ret f . next)

interpose :: (eff `Member` es, Traversable wrap) => (forall a. a -> Eff es (wrap a)) -> Handler eff es wrap -> Eff es a -> Eff es (wrap a)
interpose ret _ (Eff (Pure a)) = ret a
interpose ret f (Eff (Impure union next)) = case prj union of
  Just eff -> f eff (raise . next)
  Nothing -> Eff (Impure union (next >=> fmap sequenceA . ret))

runEff :: Eff '[] a -> a
runEff (Eff (Pure a)) = a
runEff (Eff (Impure a _)) = case a of {}

data EIO m a where
  LiftIO :: IO a -> EIO m a

-- UnliftIO :: ((forall a. m a -> IO a) -> IO b) -> EIO m b

runEffIO :: Eff '[EIO] a -> IO a
runEffIO (Eff (Pure a)) = pure a
runEffIO (Eff (Impure (This (LiftIO io)) next)) = io >>= runEffIO . fmap runIdentity . next . pure . pure
runEffIO (Eff (Impure (That union) _)) = case union of {}

instance EIO `Member` es => MonadIO (Eff es) where
  liftIO = send . LiftIO

-- instance Free c (Eff es)

-- instance EIO `Member` es => MonadUnliftIO (Eff es) where
--   withRunInIO action = send $ UnliftIO action
