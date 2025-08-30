module Theseus.Effect.Error where

import Control.Monad (join)
import Theseus.Eff

newtype Throw e m a where
  Throw :: e -> Throw e m a

throw :: Throw e `Member` es => e -> Eff ef es a
throw = send . Throw

data Catch m a where
  Catch :: Eff ef (Throw e : es) a -> (e -> Eff ef es a) -> Catch (Eff ef es) a

catch :: Catch `Member` es => Eff ef (Throw e : es) a -> (e -> Eff ef es a) -> Eff ef es a
catch action onThrow = send $ Catch action onThrow

runCatch :: Eff ef (Catch : es) a -> Eff ef es a
runCatch = handle \(Catch action onThrow) continue ->
  continue $ runThrow action >>= either onThrow pure

runThrow :: Eff ef (Throw e : es) a -> Eff ef es (Either e a)
runThrow = handleWrapped sequenceA Right \(Throw e) _ -> pure $ Left e

runCatchNoRecovery :: ef Maybe => Eff ef (Catch : es) a -> Eff ef es (Maybe a)
runCatchNoRecovery = handleRaw (fmap sequenceA) (pure . Just) \(Catch action _) continue -> do
  ran <- runCatchNoRecovery $ continue $ either (const Nothing) Just <$> runThrow action
  pure $ join ran
