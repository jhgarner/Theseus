module Theseus.Effect.Error where

import Control.Monad (join)
import Control.Monad.Identity
import Theseus.Eff

newtype Throw e m a where
  Throw :: e -> Throw e m a

throw :: Throw e `Member` es => e -> Eff ef es a
throw = send . Throw

data Catch m a where
  Catch :: ef Identity => Eff ef (Throw e : es) a -> (e -> Eff ef es a) -> Catch (Eff ef es) a

catch :: (Catch `Member` es, ef Identity) => Eff ef (Throw e : es) a -> (e -> Eff ef es a) -> Eff ef es a
catch action onThrow = send $ Catch action onThrow

runCatch :: ef Identity => Eff ef (Catch : es) a -> Eff ef es a
runCatch = fmap runIdentity . handle (pure . pure) elabCatch

elabCatch :: ef Identity => Handler Catch ef es Identity
elabCatch (Catch action onThrow) next = fmap Identity $ runCatch $ next $ runThrow action >>= either onThrow pure

runThrow :: ef Identity => Eff ef (Throw e : es) a -> Eff ef es (Either e a)
runThrow = handle (pure . pure) elabThrow

elabThrow :: Handler (Throw e) ef es (Either e)
elabThrow (Throw e) _ = pure $ Left e

runCatchNoRecovery :: ef Maybe => Eff ef (Catch : es) a -> Eff ef es (Maybe a)
runCatchNoRecovery = handleWoven (pure . Just) elabCatchNoRecovery

elabCatchNoRecovery :: ef Maybe => HandlerWoven Catch ef es Maybe
elabCatchNoRecovery (Catch action _) next = do
  ran <- runCatchNoRecovery $ next $ runThrowNoRecovery action
  pure $ join ran

runThrowNoRecovery :: ef Identity => Eff ef (Throw e : es) a -> Eff ef es (Maybe a)
runThrowNoRecovery = handle (pure . Just) elabThrowNoRecovery

elabThrowNoRecovery :: Handler (Throw e) ef es Maybe
elabThrowNoRecovery (Throw _) _ = pure Nothing
