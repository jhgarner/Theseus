{-# OPTIONS_GHC -Wno-orphans #-}

module Theseus.Effect.IO where

import Control.Exception (SomeException, throwIO, try)
import Control.Monad.IO.Class
import Theseus.Eff
import Theseus.Effect.Error

-- | An effect for IO that can throw exceptions. This is different from
-- `Final IO` because it wraps all IO actions with `try` and turns their
-- exceptions into `ExceptionalIO` effects.
data IOE :: Effect where
  LiftIO :: IO a -> IOE m a

runIOE :: (lb Identity, ExceptionalIO :> es, Final IO :> es) => Eff lb ub (IOE : es) a -> Eff lb ub es a
runIOE = interpret_ \case
  LiftIO io -> do
    ea <- send $ Final $ try @SomeException io
    case ea of
      Left e -> throw e
      Right a -> pure a

-- | The type of unhandled exceptions thrown by `IO`.
type ExceptionalIO = Throw SomeException

-- | Finishes running an IO Eff. Depending on what other effects you've run,
-- you might need to use `unrestrict` so that the first parameter contains the
-- right constraint.
runEffIO :: Eff Anything Nonthing '[IOE, ExceptionalIO, Final IO] a -> IO a
runEffIO action = do
  ea <- runEffM $ runThrow $ runIOE action
  case ea of
    -- We can safely rethrow the exception because we know there is nothing
    -- left on the effect stack that would notice.
    Left e -> throwIO e
    Right a -> pure a

-- | Runs arbitrary `IO` actions that may throw exceptions. Exceptions will be
-- caught, translated into Theseus exceptions, and re`throwIO`ed if they were not
-- handled.
instance IOE :> es => MonadIO (Eff lb ub es) where
  liftIO io = send $ LiftIO io
