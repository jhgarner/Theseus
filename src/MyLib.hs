{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
module MyLib (Eff, runEff, runEffIO, Reader(Ask, Local), runReader, ask, local) where

import Data.Kind
import Data.Coerce
import Data.Functor.Identity (Identity(runIdentity))
import Control.Monad.IO.Class (MonadIO (liftIO))
import Control.Monad.IO.Unlift (MonadUnliftIO (withRunInIO))
import Control.Monad.Cont.Class (MonadCont (callCC))


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
newtype Freer f a = Freer
  { runFreer
        :: forall m
          . MonadCont m
        => (forall x. f (Freer f) x -> m x)
        -> m a
  }
  deriving (Functor)


instance Applicative (Freer f) where
  pure a = Freer \_ -> pure a
  Freer ff <*> Freer fa = Freer \x -> ff x <*> fa x

instance Monad (Freer f) where
  Freer ma >>= fmb = Freer \x -> ma x >>= \a -> runFreer (fmb a) x

instance MonadCont (Freer f) where
  callCC f = Freer \x -> callCC (\cont -> runFreer (f (\a -> Freer \y -> y (cont a))) x)

lift :: f (Freer f) a -> Freer f a
lift f = Freer \x -> x f

raise :: Eff es a -> Eff (eff:es) a
raise (Eff (Freer freer)) = freer \x -> Eff $ lift $ That $ raiseThis x

raiseThis :: Union ls (Freer (Union es)) ~> Union ls (Freer (Union (eff:es)))
raiseThis (This eff others) = This eff (getEff . raise . Eff . others)
raiseThis (That rest) = That $ raiseThis rest

data Union (ls :: [Effect]) (f :: Type -> Type) (a :: Type) where
  This :: Testing eff => eff ogF a -> (forall x. ogF x -> f x) -> Union (eff:ls) f a
  That :: Union ls f a -> Union (eff:ls) f a

voidUnion :: Union '[] f a -> x
voidUnion ls = case ls of {}

data Reader r m a where
  Ask :: Reader r m r
  Local :: (r -> r) -> m a -> Reader r m a

ask :: Reader r `Member` es => Eff es r
ask = send Ask

local :: Reader r `Member` es => (r -> r) -> Eff es a -> Eff es a
local f = send . Local f

runReader :: r -> Eff (Reader r : es) a -> Eff es a
runReader r = handle $ elabReader r

elabReader :: r -> (m ~> Eff (Reader r: es)) -> Reader r m ~> Eff es
elabReader r _ Ask = pure r
elabReader r fix (Local f m) = handle (elabReader $ f r) $ fix m

data State s m a where
  Get :: State s m s
  Put :: s -> State s m ()

evalState :: s -> Eff (State s : es) a -> Eff es a
evalState s (Eff (Freer freer)) = Eff $ Freer \ops -> freer \case
  This Get others -> pure s
  This (Put s) others -> undefined
  That rest -> ops rest
-- elabState :: s -> (m ~> Eff (State s: es)) -> State s m ~> Eff es
-- elabState s _ Get = pure s
-- elabState _ fix (Put s) = handle (elabState $ f r) $ fix m

data Random m a where
  RandomTime :: (Eff es a -> Eff es a) -> Random (Eff es) a

type Testing :: Effect -> Constraint
type Testing eff = (forall f1 f2 a. Coercible f1 f2 => Coercible (eff f1 a) (eff f2 a))

unionTest :: _ => Eff es ()
unionTest = send $ RandomTime undefined

data TheThis eff f a where
  TheThis :: eff ogF a -> (ogF ~> f) -> TheThis eff f a

type m ~> n = forall x. m x -> n x

class Member eff es where
  inj :: eff f a -> Union es f a
  prj :: Union es f a -> Maybe (TheThis eff f a)

instance Testing eff => Member eff (eff:es) where
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

effIt :: Union ls (Freer (Union es)) a -> Union ls (Eff es) a
effIt (That rest) = That $ effIt rest
effIt (This e others) = This e (Eff . others)

type Handler eff es = (forall m. (m ~> Eff (eff:es)) -> eff m ~> Eff es)

handle :: Handler eff es -> Eff (eff:es) a -> Eff es a
handle f (Eff (Freer freer)) = freer (matchTop f)

matchTop :: Handler eff es -> Union (eff:es) (Freer (Union (eff:es))) a -> Eff es a
matchTop f (This eff others) = f (Eff . others) eff
matchTop f (That rest) = Eff (Freer \x -> x $ matchInners f rest)

matchInners :: Handler eff es -> Union ls (Freer (Union (eff:es))) a -> Union ls (Freer (Union es)) a
matchInners f (This oEff others) = This oEff (getEff . handle f . Eff . others)
matchInners f (That rest) = That $ matchInners f rest

type Interposer eff es = (forall m. (m ~> Eff es) -> eff m ~> Eff es)

interpose :: eff `Member` es => Interposer eff es -> Eff es a -> Eff es a
interpose new (Eff (Freer freer)) =
  freer $ \op -> maybe (Eff $ lift op) (\(TheThis eff others) -> new (Eff . others) eff) $ prj op

runEff :: Eff '[] a -> a
runEff (Eff (Freer ops)) = runIdentity $ ops voidUnion

data EIO m a where
  LiftIO :: IO a -> EIO m a
  UnliftIO :: ((forall a. m a -> IO a) -> IO b) -> EIO m b


runEffIO :: Eff '[EIO] a -> IO a
runEffIO (Eff (Freer ops)) = ops matchIO

matchIO :: Union '[EIO] (Freer (Union '[EIO])) a -> IO a
matchIO (This (LiftIO io) _) = io
matchIO (This (UnliftIO unlift) others) = unlift $ runEffIO . Eff . others
matchIO (That empty) = voidUnion empty

instance EIO `Member` es => MonadIO (Eff es) where
  liftIO = send . LiftIO 

instance EIO `Member` es => MonadUnliftIO (Eff es) where
  withRunInIO action = send $ UnliftIO action
