module Theseus.Effect.Output where

import Theseus.Eff

data Output w :: Effect where
  Output :: w -> Output w m ()

output :: Output w `Member` es => w -> Eff ef es ()
output w = send $ Output w

type OutputResult w = ((,) w)

runOutput :: (Monoid w, ef (OutputResult w)) => Eff ef (Output w : es) a -> Eff ef es (OutputResult w a)
runOutput = go mempty
 where
  go :: (Monoid w, ef (OutputResult w)) => w -> Eff ef (Output w : es) a -> Eff ef es (OutputResult w a)
  go soFar = interpretW_ (soFar,) $ \(Output w) -> pure ((), go $ soFar <> w)
