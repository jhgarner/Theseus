module Theseus.Effect.Output where

import Theseus.Eff

-- | This is a Writer without the higher order action.
data Output w :: Effect where
  Output :: w -> Output w m ()

output :: Output w :> es => w -> Eff lb ub es ()
output w = send $ Output w

type OutputResult w = ((,) w)

runOutput :: (Monoid w, lb (OutputResult w)) => Eff lb ub (Output w : es) a -> Eff lb ub es (OutputResult w a)
runOutput = go mempty
 where
  go :: (Monoid w, lb (OutputResult w)) => w -> Eff lb ub (Output w : es) a -> Eff lb ub es (OutputResult w a)
  go soFar = interpretW_ (\a -> pure (soFar, a)) $ \(Output w) -> (pure (), go $ soFar <> w)

execOutput :: (Monoid w, lb (OutputResult w)) => Eff lb ub (Output w : es) a -> Eff lb ub es w
execOutput = fmap fst . runOutput
