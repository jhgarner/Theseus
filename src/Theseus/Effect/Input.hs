module Theseus.Effect.Input where

import Control.Monad.Identity
import Theseus.Eff

-- | This is a Reader without the Local action.
data Input i :: Effect where
  Input :: Input i m i

input :: Input i :> es => Eff lb ub es i
input = send Input

runInput :: lb Identity => i -> Eff lb ub (Input i : es) a -> Eff lb ub es a
runInput i = interpret_ \Input -> pure i

-- | Create a resource with a finalizer that's guaranteed to run. The resource
-- will be accessible using the `Input` effect.
resource :: lb Identity => Eff lb ub es i -> (i -> Eff lb ub es ()) -> Eff lb ub (Input i : es) a -> Eff lb ub es a
resource init finalizer act = do
  i <- init
  finally (runInput i act) (finalizer i)
