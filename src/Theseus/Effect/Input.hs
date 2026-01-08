module Theseus.Effect.Input where

import Control.Monad.Identity
import Data.Functor
import Theseus.Eff
import Theseus.Interpreters (IdentityCf (IdentityCf, runIdentityCf))

-- | This is a Reader without the Local action.
data Input i :: Effect where
  Input :: Input i m i

input :: Input i `Member` es => Eff ef es i
input = send Input

runInput :: ef Identity => i -> Eff ef (Input i : es) a -> Eff ef es a
runInput i = interpret_ \Input -> pure i

-- | Create a resource with a finalizer that's guaranteed to run. The resource
-- will be accessible using the `Input` effect.
resource :: ef Identity => Eff ef es i -> (i -> Eff ef es ()) -> Eff ef (Input i : es) a -> Eff ef es a
resource @ef @es @i init finalizer act = do
  i <- init
  runIdentity <$> runIt i act
 where
  runIt :: ef Identity => i -> Eff ef (Input i : es) a -> Eff ef es (Identity a)
  runIt i = interpretRaw (\x -> finalizer i $> Identity x) \Input _ next ->
    runIt i $ runIdentityCf $ next $ IdentityCf $ pure i
