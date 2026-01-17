module Theseus.Effect.Writer where

import Data.Functor
import Theseus.Eff

-- # Writer

-- The writer is a more complicated effect which combines higher order
-- operations with changing the return type.

-- | An effect equivalent to the popular `MonadWriter` class.
data Writer w :: Effect where
  Tell :: w -> Writer w m ()
  Listen :: ef (WriterResult w) => Eff ef (Writer w : es) a -> Writer w (Eff ef es) (w, a)
  Pass :: ef (WriterResult w) => Eff ef (Writer w : es) (w -> w, a) -> Writer w (Eff ef es) a

-- | Adds a value to the output
tell :: Writer w :> es => w -> Eff ef es ()
tell w = send $ Tell w

-- | listens in on the computation's output without ignoring the output.
listen :: Writer w :> es => ef (WriterResult w) => Eff ef (Writer w : es) a -> Eff ef es (w, a)
listen action = send $ Listen action

-- | Uses the returned function to modify the output before it's accumulated.
pass :: Writer w :> es => ef (WriterResult w) => Eff ef (Writer w : es) (w -> w, a) -> Eff ef es a
pass action = send $ Pass action

-- | Runs a writer that acts like the popular `WriterT` Monad. The output will
-- begin as `mempty` and be accumulated using `<>`.
runWriter :: (ef (WriterResult w), Monoid w) => Eff ef (Writer w : es) a -> Eff ef es (w, a)
runWriter = runWriterFrom mempty (\_ -> pure ())

type WriterResult w = ((,) w)

-- | Runs a writer using a specific initial value (the first parameter) and
-- a finalizer to run at the end (the second parameter). The finalizer is used
-- by the implemetation of `listen` to make sure the output isn't lost when
-- there are exceptions.
runWriterFrom :: (Monoid w, ef (WriterResult w)) => w -> (w -> Eff ef es ()) -> Eff ef (Writer w : es) a -> Eff ef es (w, a)
runWriterFrom @w start end = interpretW (\a -> end start $> (start, a)) $ \sender eff ->
  pure (sender @(Writer w) elabWriter eff, runWriterFrom (start <> told eff) end)
 where
  elabWriter ::
    (Monoid w, Writer w :> es) =>
    Writer w (Eff ef es) x ->
    Eff ef es x
  elabWriter (Tell _) = pure ()
  -- The difference between `listen`'s implementation and `pass`'s
  -- implementation show the difference between non-transactional and
  -- transactional state. When the `tell` is part of the finalizer, it
  -- always runs even if the higher order operation throws an exception. That
  -- makes it non-transactional. When the `tell` is part of the do block, it
  -- only runs if the higher order operation finished successfully. That makes
  -- it transactional. Why does `Writer` contain transactional and
  -- non-transactional operations? Wouldn't it make more sense for both to be
  -- non-transactional? Well the `pass` operation requires the output
  -- be transformed by part of the return value (that's the function that the
  -- higher order operation returns). We only have that function if the higher
  -- order operation completes successfully. That means `pass` must be
  -- transactional because we can only commit the transaction if we got the
  -- return value.
  elabWriter (Listen action) = runWriterFrom mempty tell action
  elabWriter (Pass action) = do
    (w, (f, a)) <- runWriterFrom mempty (\_ -> pure ()) action
    tell $ f w
    pure a

  told :: Monoid w => Writer w m x -> w
  told (Tell w) = w
  told _ = mempty
