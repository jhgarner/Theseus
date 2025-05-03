{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}

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
import Data.Type.Equality

type Effect = (Type -> Type) -> Type -> Type

type data Requires = Morphism | Complex

type Freer :: Requires -> [Effect] -> Type -> Type
data Freer r es a where
  Pure :: a -> Freer r es a
  Impure :: (Union es esSend x) -> (Eff esSend x -> Eff (ES Complex es) a) -> Freer Complex es a
  Simple :: (Union es esSend x) -> (forall z. Eff esSend z -> Eff (ES Morphism es) z) -> (x -> Eff (ES Morphism es) a) -> Freer Morphism es a

asComplex :: Freer r es a -> Freer Complex es a
asComplex (Pure a) = Pure a
asComplex (Impure union next) = Impure union next
asComplex (Simple union trans next) = Impure union (Eff . asComplex . getEff . trans >=> Eff . asComplex . getEff . next)

deriving instance Functor (Freer r h)

instance Applicative (Freer r f) where
  pure = Pure

  Pure f <*> rhs = fmap f rhs
  Impure eff next <*> m = Impure eff \x -> next x <*> Eff m
  Simple eff others next <*> m = Simple eff others \x -> next x <*> Eff m

instance Monad (Freer r f) where
  Pure ma >>= fmb = fmb ma
  Impure eff next >>= fmb = Impure eff \x -> next x >>= Eff . fmb
  Simple eff morph next >>= fmb = Simple eff morph \x -> next x >>= Eff . fmb

-- Simple eff others next >>= fmb = Simple eff others \x -> next x >>= Eff . fmb

class Liftable r where
  lift :: Union es (ES r es) a -> Freer r es a

instance Liftable Complex where
  lift f = Impure f id

instance Liftable Morphism where
  lift f = Simple f id pure

raise :: Eff (ES r es) a -> Eff (ES r (eff : es)) a
raise (Eff (Pure a)) = pure a
raise (Eff (Impure eff next)) = Eff $ Impure (raiseEff eff) (raise . next)
raise (Eff (Simple eff morph next)) = Eff $ Simple (raiseEff eff) (raise . morph) (raise . next)

raiseEff :: Union es esSend x -> Union (eff : es) esSend x
raiseEff (This eff) = That (This eff)
raiseEff (That rest) = That $ raiseEff rest

data Union (ls :: [Effect]) (es :: EffState) (a :: Type) where
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

runReader :: r -> Eff (Reader r `Prep` es) a -> Eff es a
runReader r = handle pure $ elabReader r

elabReader :: r -> Handler (Reader r) es a a
elabReader r Ask next = runReader r $ next $ pure r
elabReader r (Local f m) next = runReader r $ next $ interpose pure (elabReader $ f r) $ m

data State s m a where
  Get :: State s m s
  Put :: s -> State s m ()

get :: State s `Member` es => Eff es s
get = send Get

gets :: State s `Member` es => (s -> a) -> Eff es a
gets = (<$> send Get)

put :: State s `Member` es => s -> Eff es ()
put = send . Put

runState :: s -> Eff (State s `Prep` es) a -> Eff es (s, a)
runState s = handle (pure . (s,)) $ elabState s

elabState :: s -> Handler (State s) es a (s, a)
elabState s Get next = runState s $ next $ pure s
elabState _ (Put s') next = runState s' $ next $ pure ()

execState :: s -> Eff (State s `Prep` es) a -> Eff es s
execState s = fmap fst . runState s

evalState :: s -> Eff (State s `Prep` es) a -> Eff es a
evalState s = fmap snd . runState s

newtype Throw e m a where
  Throw :: e -> Throw e m a

throw :: Throw e `Member` es => e -> Eff es a
throw = send . Throw

data Catch m a where
  Catch :: Eff (Throw e `Prep` es) a -> (e -> Eff es a) -> Catch (Eff es) a

catch :: Catch `Member` es => Eff (Throw e `Prep` es) a -> (e -> Eff es a) -> Eff es a
catch action onThrow = send $ Catch action onThrow

runCatch :: Eff (Catch `Prep` es) a -> Eff es a
runCatch = handle pure elabCatch

elabCatch :: Handler Catch es a a
elabCatch (Catch action onThrow) next = runCatch $ next $ runThrow onThrow action

runThrow :: (e -> Eff es a) -> Eff (Throw e `Prep` es) a -> Eff es a
runThrow onThrow = handle pure $ elabThrow onThrow

elabThrow :: (e -> Eff es a) -> Handler (Throw e) es a a
elabThrow onThrow (Throw e) _ = onThrow e

class InternalMember eff ls where
  internalInj :: eff (Eff es) a -> Union ls es a
  internalPrj :: Union ls es a -> Maybe (eff (Eff es) a)

instance InternalMember eff (eff : es) where
  internalInj eff = This eff

  internalPrj (This eff) = Just eff
  internalPrj (That _) = Nothing

instance {-# OVERLAPPABLE #-} InternalMember eff es => InternalMember eff (other : es) where
  internalInj eff = That $ internalInj eff

  internalPrj (This _) = Nothing
  internalPrj (That rest) = internalPrj rest

class (InternalMember eff (GetEffects es), Liftable (GetRequires es)) => Member eff (es :: EffState) where
  inj :: eff (Eff es) a -> Union (GetEffects es) es a

-- class (InternalMember eff es, Liftable r) => HMember eff (es :: [Effect]) (r :: Requires) where
--   inj :: eff (Eff (ES es r)) a -> Union es (ES es r) a

prj :: InternalMember eff ls => Union ls es a -> Maybe (eff (Eff es) a)
prj = internalPrj

instance (InternalMember eff (GetEffects es), Liftable (GetRequires es)) => Member eff es where
  inj = internalInj

type data EffState = ES Requires [Effect]
type family GetRequires (es :: EffState) :: Requires where
  GetRequires (ES requires _) = requires

type family GetEffects (es :: EffState) :: [Effect] where
  GetEffects (ES _ es) = es

type family Prep (eff :: Effect) (es :: EffState) = (result :: EffState) | result -> eff es where
  Prep eff (ES r es) = ES r (eff : es)

newtype Eff (es :: EffState) a = Eff {getEff :: (Freer (GetRequires es) (GetEffects es) a)}
  deriving (Functor, Applicative, Monad)

isEq :: es ~ ES r ess => es :~: ES (GetRequires es) (GetEffects es)
isEq = Refl

send :: eff `Member` es => eff (Eff es) a -> Eff es a
send eff = case isEq of Refl -> Eff $ lift $ inj $ eff

type Handler eff es a ans = (forall esSend x. eff (Eff esSend) x -> (Eff esSend x -> Eff (eff `Prep` es) a) -> Eff es ans)

handle :: (a -> Eff es ans) -> Handler eff es a ans -> Eff (eff `Prep` es) a -> Eff es ans
handle ret _ (Eff (Pure a)) = ret a
handle _ f (Eff (Impure (This e) next)) = f e (next)
handle ret f (Eff (Impure (That rest) next)) = Eff $ Impure rest (handle ret f . next)

interpose :: eff `Member` es => (a -> Eff es ans) -> Handler eff es a ans -> Eff es a -> Eff es ans
interpose ret _ (Eff (Pure a)) = ret a
interpose ret f (Eff (Impure union next)) = case prj union of
  Just eff -> f eff (raise . next)
  Nothing -> Eff (Impure union (next >=> ret))

runEff :: Eff (ES r '[]) a -> a
runEff (Eff (Pure a)) = a
runEff (Eff (Impure a _)) = case a of {}

data EIO m a where
  LiftIO :: IO a -> EIO m a

-- UnliftIO :: ((forall a. m a -> IO a) -> IO b) -> EIO m b

runEffIO :: Eff (ES r '[EIO]) a -> IO a
runEffIO (Eff (Pure a)) = pure a
runEffIO (Eff (Impure (This (LiftIO io)) next)) = io >>= runEffIO . next . pure
runEffIO (Eff (Impure (That union) _)) = case union of {}

instance EIO `Member` es => MonadIO (Eff es) where
  liftIO = send . LiftIO

-- instance Free c (Eff es)

-- instance EIO `Member` es => MonadUnliftIO (Eff es) where
--   withRunInIO action = send $ UnliftIO action
