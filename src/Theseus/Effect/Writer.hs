module Theseus.Effect.Writer where

import Theseus.Eff

-- # Writer

-- The writer is a more complicated higher order effect. Notably it is not
-- a scoped effect.

data Writer w :: Effect where
  Tell :: w -> Writer w m ()
  Listen :: ef (WriterResult w) => Eff ef (Writer w : es) a -> Writer w (Eff ef es) (w, a)
  Pass :: ef (WriterResult w) => Eff ef (Writer w : es) (w -> w, a) -> Writer w (Eff ef es) a

tell :: Writer w `Member` es => w -> Eff ef es ()
tell w = send $ Tell w

listen :: Writer w `Member` es => ef (WriterResult w) => Eff ef (Writer w : es) a -> Eff ef es (w, a)
listen action = send $ Listen action

pass :: Writer w `Member` es => ef (WriterResult w) => Eff ef (Writer w : es) (w -> w, a) -> Eff ef es a
pass action = send $ Pass action

runWriter :: (ef (WriterResult w), Monoid w) => Eff ef (Writer w : es) a -> Eff ef es (w, a)
runWriter = runWriterFrom mempty

type WriterResult w = ((,) w)

runWriterFrom :: (Monoid w, ef (WriterResult w)) => w -> Eff ef (Writer w : es) a -> Eff ef es (w, a)
runWriterFrom @w start = interpretW (start,) $ \sender eff ->
  pure (sender @(Writer w) elabWriter eff, runWriterFrom $ start <> told eff)
 where
  elabWriter ::
    (Monoid w, Writer w `Member` es) =>
    Writer w (Eff ef es) x ->
    Eff ef es x
  elabWriter (Tell _) = pure ()
  elabWriter (Listen action) = do
    (w, a) <- runWriterFrom mempty action
    tell w
    pure (w, a)
  elabWriter (Pass action) = do
    (w, (f, a)) <- runWriterFrom mempty action
    tell $ f w
    pure a

  told :: Monoid w => Writer w m x -> w
  told (Tell w) = w
  told _ = mempty
