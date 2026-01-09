module Theseus.Effect.Reader (
  Reader (Ask, Local),
  ask,
  local,
  asks,
  runReader,
  runReaderNoLocal,
) where

import Theseus.Eff

-- # Reader

-- The Reader effect is a good example of a higher order effect because it's
-- otherwise very simple.

-- | Computations that use `Reader r` can ask the environment for some `r`.
-- They cannot change the `r`, but that does not necessarily mean that two
-- calls to `ask` will never return different `r`s. For example, if a call to
-- `yield` happens between the asks, the implementation might be switched out
-- for another.
data Reader r m a where
  Ask :: Reader r m r
  -- Local is a provider for Readers. It seems like many higher order effects
  -- follow the pattern of being providers for other effects. Sometimes the
  -- provider-ness is hidden behind `interpose`, but it's still there. In
  -- Theseus I'm trying to make that explicit which is why there's a new
  -- `Reader r` constraint on top. Other effect systems (and earlier versions
  -- of Theseus) use `interpose` to hide the new effect. I don't think that's
  -- necessary. The only downside I can see is it makes it possible to skip the
  -- local reader with `raise`. I don't know if that's actually bad though.
  Local :: ef Identity => (r -> r) -> Eff ef (Reader r : es) a -> Reader r (Eff ef es) a

-- | Returns the `Reader`'s constant value.
ask :: Reader r `Member` es => Eff ef es r
ask = send Ask

-- | Modifies the `Reader`'s value within some limited scope.
local :: ef Identity => Reader r `Member` es => (r -> r) -> Eff ef (Reader r : es) a -> Eff ef es a
local f action = send $ Local f action

-- | A convenience function equivalent to `fmap f ask`.
asks :: Reader r `Member` es => (r -> a) -> Eff ef es a
asks f = fmap f ask

-- | Runs a `Reader r` effect with the generally expected semantics.
runReader :: forall r ef es a. ef Identity => r -> Eff ef (Reader r : es) a -> Eff ef es a
runReader r = interpret \sender -> \case
  Ask -> pure $ pure r
  -- Here's an example of `sender` being used so that we can share the `Reader
  -- r` that we're interpreting with the `Local` sender.
  Local f m -> pure $ sender @(Reader r) $ localReader f m

-- | A `runReader` that modifies the result of an inner `Reader r`.
localReader :: forall r ef es a. (ef Identity, Reader r `Member` es) => (r -> r) -> Eff ef (Reader r : es) a -> Eff ef es a
localReader f = interpret \sender -> \case
  Ask -> pure . f <$> ask
  Local newF m -> pure $ sender @(Reader r) $ localReader (newF . f) m

-- | This is a version of Reader which completely ignores the function passed
-- to local. It's pointless and you should never use it, but it illustrates one
-- of the challenges with Coroutine.
runReaderNoLocal :: ef Identity => r -> Eff ef (Reader r : es) a -> Eff ef es a
runReaderNoLocal @_ @r r = interpret \sender -> \case
  Ask -> pure $ pure r
  Local _ m -> pure (sender @(Reader r) $ locallyRunReaderNoLocal m)

locallyRunReaderNoLocal :: (Reader r `Member` es, ef Identity) => Eff ef (Reader r : es) a -> Eff ef es a
locallyRunReaderNoLocal @r = interpret \sender -> \case
  Ask -> pure <$> ask
  Local _ m -> pure (sender @(Reader r) $ locallyRunReaderNoLocal m)
