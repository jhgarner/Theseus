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
) where

import Control.Monad.IO.Class (MonadIO (liftIO))
import Data.Kind

-- import Control.Monad.IO.Unlift (MonadUnliftIO (withRunInIO))

import Control.Monad ((>=>))

type Effect = (Type -> Type) -> Type -> Type

type Freer :: [Effect] -> Type -> Type
data Freer es a
  = Pure a
  | forall (esSend :: [Effect]) x. Impure (Union es esSend x) (Eff esSend x -> Eff es a)

deriving instance Functor (Freer h)

instance Applicative (Freer f) where
  pure = Pure

  Pure f <*> rhs = fmap f rhs
  Impure eff next <*> m = Impure eff \x -> next x <*> Eff m

instance Monad (Freer f) where
  Pure ma >>= fmb = fmb ma
  Impure eff next >>= fmb = Impure eff (next >=> (Eff . fmb))

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
runReader r = handle pure $ elabReader r

elabReader :: r -> Handler (Reader r) es a a
elabReader r Ask next = runReader r $ next $ pure r
elabReader r (Local f m) next = runReader r $ next $ interpose pure (elabReader $ f r) m

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

elabState :: s -> Handler (State s) es a (s, a)
elabState s Get next = runState s $ next $ pure s
elabState _ (Put s') next = runState s' $ next $ pure ()

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
runCatch = handle pure elabCatch

elabCatch :: Handler Catch es a a
elabCatch (Catch action onThrow) next = runCatch $ next $ runThrow onThrow action

runThrow :: (e -> Eff es a) -> Eff (Throw e : es) a -> Eff es a
runThrow onThrow = handle pure $ elabThrow onThrow

elabThrow :: (e -> Eff es a) -> Handler (Throw e) es a a
elabThrow onThrow (Throw e) _ = onThrow e

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

type Handler eff es a ans = (forall esSend x. eff (Eff esSend) x -> (Eff esSend x -> Eff (eff : es) a) -> Eff es ans)

handle :: (a -> Eff es ans) -> Handler eff es a ans -> Eff (eff : es) a -> Eff es ans
handle ret _ (Eff (Pure a)) = ret a
handle _ f (Eff (Impure (This e) next)) = f e next
handle ret f (Eff (Impure (That rest) next)) = Eff $ Impure rest (handle ret f . next)

interpose :: eff `Member` es => (a -> Eff es ans) -> Handler eff es a ans -> Eff es a -> Eff es ans
interpose ret _ (Eff (Pure a)) = ret a
interpose ret f (Eff (Impure union next)) = case prj union of
  Just eff -> f eff (raise . next)
  Nothing -> Eff (Impure union (next >=> ret))

runEff :: Eff '[] a -> a
runEff (Eff (Pure a)) = a
runEff (Eff (Impure a _)) = case a of {}

data EIO m a where
  LiftIO :: IO a -> EIO m a

-- UnliftIO :: ((forall a. m a -> IO a) -> IO b) -> EIO m b

runEffIO :: Eff '[EIO] a -> IO a
runEffIO (Eff (Pure a)) = pure a
runEffIO (Eff (Impure (This (LiftIO io)) next)) = io >>= runEffIO . next . pure
runEffIO (Eff (Impure (That union) _)) = case union of {}

instance EIO `Member` es => MonadIO (Eff es) where
  liftIO = send . LiftIO

-- instance Free c (Eff es)

-- instance EIO `Member` es => MonadUnliftIO (Eff es) where
--   withRunInIO action = send $ UnliftIO action
