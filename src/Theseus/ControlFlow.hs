{-# LANGUAGE DeepSubsumption #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Theseus.ControlFlow where

import Theseus.EffType

newtype IdentityCf eff f a = IdentityCf {runIdentityCf :: f a}
  deriving (Functor)

instance ControlFlow IdentityCf Boring where
  IdentityCf fab `cfApply` fa = IdentityCf $ fab <*> fa
  IdentityCf fa `cfBind` afb = IdentityCf $ fa >>= afb
  cfMap _ efToOut (IdentityCf fa) = IdentityCf $ efToOut fa
  cfRun _ handler (IdentityCf fa) = IdentityCf $ handler fa

newtype MaybeCf eff f a = MaybeCf {runMaybeCf :: f (Maybe a)}
  deriving (Functor)

instance ControlFlow MaybeCf Traversable where
  MaybeCf fmab `cfApply` fa = MaybeCf $ (\mab a -> fmap ($ a) mab) <$> fmab <*> fa
  MaybeCf fma `cfBind` afb = MaybeCf $ fma >>= traverse afb
  cfMap _ efToOut (MaybeCf fa) = MaybeCf $ efToOut fa
  cfRun _ handler (MaybeCf fa) = MaybeCf $ sequenceA <$> handler fa

newtype ConstCf e eff f a = ConstCf {getConstCf :: e}
  deriving (Functor)

instance ControlFlow (ConstCf e) Boring where
  ConstCf e `cfApply` _ = ConstCf e
  ConstCf e `cfBind` _ = ConstCf e
  cfMap _ _ (ConstCf e) = ConstCf e
  cfRun _ handler (ConstCf e) = ConstCf e

--
-- deriving via IsHFunctor (Comp e) instance WeakHFunctor (Comp e)
-- instance ControlFlow (Comp m) Boring where
--   (mx :>>= xga) `cfApply` fa = mx :>>= \x -> xga x <*> fa
--   (mx :>>= xga) `cfBind` afb = mx :>>= (xga >=> afb)
--   handler `cfRun` (mx :>>= xga) = mx :>>= (handler . xga)

newtype ComposeCf f eff g a = ComposeCf {getComposeCf :: f (g a)}
  deriving (Functor)

instance Functor m => ControlFlow (ComposeCf m) Boring where
  ComposeCf mfab `cfApply` fa = ComposeCf $ fmap (<*> fa) mfab
  ComposeCf mfa `cfBind` afb = ComposeCf $ fmap (>>= afb) mfa
  cfMap _ handler (ComposeCf mfa) = ComposeCf $ fmap handler mfa
  cfRun _ handler (ComposeCf mfa) = ComposeCf $ fmap handler mfa

--
-- deriving via IsHFunctor ProxyF instance WeakHFunctor ProxyF
-- instance ControlFlow ProxyF Boring where
--   ProxyF `cfApply` _ = ProxyF
--   ProxyF `cfBind` _ = ProxyF
--   _ `cfRun` ProxyF = ProxyF

-- data Both m a = Both (m a) (m a)
--   deriving (Functor)
--
-- instance HFunctor Both where
--   handler `hmap` Both lhs rhs = Both (handler lhs) (handler rhs)
--
-- instance ControlFlow Both Boring where
--   Both lfab rfab `cfApply` fa = Both (lfab <*> fa) (rfab <*> fa)
--   Both lfa rfa `cfBind` afb = Both (lfa >>= afb) (rfa >>= afb)
--   handler `cfRun` Both lfa rfa = Both (handler lfa) (handler rfa)

-- instance HFunctor Phases where
--   handler `hmap` Lift both = Lift $ handler both
--   handler `hmap` (this :<*> rest) = handler this :<*> hmap handler rest
--
-- instance ControlFlow Phases Functor where
--   Both fab `cfApply` fa = Both $ liftA2 (\(lhs, rhs) a -> (lhs a, rhs a)) fab fa
--   Both fa `cfBind` afb = Both $ fa >>= (uncurry (liftA2 (,)) . bimap afb afb)
--   handler `cfRun` Both fa = Both $ (\waa -> (fmap fst waa, fmap snd waa)) <$> handler fa

-- newtype Both m a = Both {getBoth :: m (a, a)}
--   deriving (Functor)
--
-- instance HFunctor Both where
--   handler `hmap` Both both = Both $ handler both
--
-- instance ControlFlow Both Functor where
--   Both fab `cfApply` fa = Both $ liftA2 (\(lhs, rhs) a -> (lhs a, rhs a)) fab fa
--   Both fa `cfBind` afb = Both $ fa >>= (uncurry (liftA2 (,)) . bimap afb afb)
--   handler `cfRun` Both fa = Both $ (\waa -> (fmap fst waa, fmap snd waa)) <$> handler fa
