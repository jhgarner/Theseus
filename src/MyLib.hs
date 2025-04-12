{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
module MyLib (Eff, runEff, runEffIO, raise, Reader(Ask, Local), runReader, ask, local, asks, State(Get, Put), evalState, execState, runState, get, put, gets) where

import Data.Kind
import Control.Monad.IO.Class (MonadIO (liftIO))
import Control.Monad.IO.Unlift (MonadUnliftIO (withRunInIO))
import Control.Monad ((>=>))


type Effect = (Type -> Type) -> Type -> Type

-- type Freeish :: Effect -> Type -> Type
-- newtype Freeish f a = Freeish
--   { runFreer
--         :: forall m
--           . Monad m
--         => (forall x. f (Freer f) x -> m x)
--         -> m a
--   }
--   deriving (Functor)

type Freer :: Effect -> Type -> Type
data Freer h a
  = Pure a
  | forall x. Impure (h (Freer h) x) (x -> Freer h a)

deriving instance Functor (Freer h)

instance Applicative (Freer f) where
  pure = Pure

  Pure f <*> rhs = fmap f rhs
  Impure eff next <*> m = Impure eff \x -> next x <*> m

instance Monad (Freer f) where
  Pure ma >>= fmb = fmb ma
  Impure eff next >>= fmb = Impure eff $ next >=> fmb

lift :: f (Freer f) a -> Freer f a
lift f = Impure f Pure

raise :: Eff es a -> Eff (eff:es) a
raise (Eff (Pure a)) = pure a
raise (Eff (Impure eff next)) = Eff $ Impure (That $ raiseThis eff) (getEff . raise . Eff . next)

raiseThis :: Union ls (Freer (Union es)) ~> Union ls (Freer (Union (eff:es)))
raiseThis (This eff others) = This eff (getEff . raise . Eff . others)
raiseThis (That rest) = That $ raiseThis rest

data Union (ls :: [Effect]) (f :: Type -> Type) (a :: Type) where
  This :: eff ogF a -> (forall x. ogF x -> f x) -> Union (eff:ls) f a
  That :: Union ls f a -> Union (eff:ls) f a

data Reader r m a where
  Ask :: Reader r m r
  Local :: (r -> r) -> m a -> Reader r m a

ask :: Reader r `Member` es => Eff es r
ask = send Ask

asks :: Reader r `Member` es => (r -> a) -> Eff es a
asks = (<$> ask)

local :: Reader r `Member` es => (r -> r) -> Eff es a -> Eff es a
local f = send . Local f

runReader :: r -> Eff (Reader r : es) a -> Eff es a
runReader r = handle $ \cases
  _ Ask next -> runReader r $ next r
  fix (Local f m) next -> (runReader (f r) $ fix m) >>= runReader r . next

data State s m a where
  Get :: State s m s
  Put :: s -> State s m ()

get :: State s `Member` es => Eff es s
get = send Get

gets :: State s `Member` es => (s -> a) -> Eff es a
gets = (<$> send Get)

put :: State s `Member` es => s -> Eff es ()
put = send . Put

evalState :: s -> Eff (State s : es) a -> Eff es a
evalState s = handle $ \cases
  _ Get next -> evalState s $ next s
  _ (Put s') next -> evalState s' $ next ()

execState :: s -> Eff (State s : es) a -> Eff es s
execState s actions = evalState s $ actions *> get

runState :: s -> Eff (State s : es) a -> Eff es (s, a)
runState s actions = evalState s do
  a <- actions
  s <- get
  pure (s, a)

data TheThis eff f a where
  TheThis :: eff ogF a -> (ogF ~> f) -> TheThis eff f a

type m ~> n = forall x. m x -> n x

class Member eff es where
  inj :: eff f a -> Union es f a
  prj :: Union es f a -> Maybe (TheThis eff f a)

instance Member eff (eff:es) where
  inj eff = This eff id

  prj (This eff others) = Just $ TheThis eff others
  prj (That _) = Nothing

instance {-# OVERLAPPABLE #-} Member eff es => Member eff (other:es) where
  inj eff = That $ inj eff

  prj (This _ _) = Nothing
  prj (That rest) = prj rest

newtype Eff (ls :: [Effect]) a = Eff { getEff :: Freer (Union ls) a}
  deriving (Functor, Applicative, Monad)

send :: eff `Member` es => eff (Eff es) a -> Eff es a
send eff = Eff $ lift $ unEff $ inj $ eff

unEff :: Union ls (Eff es) a -> Union ls (Freer (Union es)) a
unEff (That rest) = That $ unEff rest
unEff (This e others) = This e (getEff . others)

-- effIt :: Union ls (Freer (Union es)) a -> Union ls (Eff es) a
-- effIt (That rest) = That $ effIt rest
-- effIt (This e others) = This e (Eff . others)

type Handler eff es = (forall m. (m ~> Eff (eff:es)) -> forall x a. eff m x -> (x -> Eff (eff:es) a) -> Eff es a)

handle :: Handler eff es -> Eff (eff:es) a -> Eff es a
handle _ (Eff (Pure a)) = Eff $ Pure a
handle f (Eff (Impure (This e others) next)) = f (Eff . others) e (Eff . next)
handle f (Eff (Impure (That rest) next)) = Eff (lift (matchInners f rest)) >>= handle f . Eff . next

matchInners :: Handler eff es -> Union ls (Freer (Union (eff:es))) a -> Union ls (Freer (Union es)) a
matchInners f (This oEff others) = This oEff (getEff . handle f . Eff . others)
matchInners f (That rest) = That $ matchInners f rest

-- type Interposer eff es = (forall m. (m ~> Eff es) -> eff m ~> Eff es)

-- interpose :: eff `Member` es => Interposer eff es -> Eff es a -> Eff es a
-- interpose new (Eff (Freer freer)) =
--   freer $ \op -> maybe (Eff $ lift op) (\(TheThis eff others) -> new (Eff . others) eff) $ prj op

runEff :: Eff '[] a -> a
runEff (Eff (Pure a)) = a
runEff (Eff (Impure a _)) = case a of {}

data EIO m a where
  LiftIO :: IO a -> EIO m a
  UnliftIO :: ((forall a. m a -> IO a) -> IO b) -> EIO m b


runEffIO :: Eff '[EIO] a -> IO a
runEffIO (Eff (Pure a)) = pure a
runEffIO (Eff (Impure (This (LiftIO io) _) rest)) = Eff . rest <$> io >>= runEffIO
runEffIO (Eff (Impure (This (UnliftIO unlift) others) rest)) = (Eff . rest <$> unlift (runEffIO . Eff . others)) >>= runEffIO
runEffIO (Eff (Impure (That union) _)) = case union of {}

instance EIO `Member` es => MonadIO (Eff es) where
  liftIO = send . LiftIO 

instance EIO `Member` es => MonadUnliftIO (Eff es) where
  withRunInIO action = send $ UnliftIO action
