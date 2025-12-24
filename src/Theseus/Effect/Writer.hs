module Theseus.Effect.Writer where

import Theseus.Eff

data Writer w :: Effect where
  Tell :: w -> Writer w m ()
  Listen :: ef (WriterResult w) => Eff ef es a -> Writer w (Eff ef es) (w, a)
  Pass :: ef (WriterResult w) => Eff ef es (w -> w, a) -> Writer w (Eff ef es) a

tell :: Writer w `Member` es => w -> Eff ef es ()
tell w = send $ Tell w

listen :: Writer w `Member` es => ef (WriterResult w) => Eff ef es a -> Eff ef es (w, a)
listen action = send $ Listen action

pass :: Writer w `Member` es => ef (WriterResult w) => Eff ef es (w -> w, a) -> Eff ef es a
pass action = send $ Pass action

runWriter :: (ef (WriterResult w), Monoid w) => Eff ef (Writer w : es) a -> Eff ef es (w, a)
runWriter = runWriterFrom mempty

type WriterResult w = ((,) w)

runWriterFrom :: (ef (WriterResult w), Monoid w) => w -> Eff ef (Writer w : es) a -> Eff ef es (w, a)
runWriterFrom start = handleWrapped (start,) $ elabWriter runWriterFrom start

interposeWriter :: (ef (WriterResult w), Writer w `Member` es, Monoid w) => w -> Eff ef es a -> Eff ef es (w, a)
interposeWriter start = interposeWrapped (start,) $ elabWriter interposeWriter start

elabWriter ::
  (Writer w `Member` es, Monoid w) =>
  (w -> Eff ef' es' a -> r) ->
  w ->
  Writer w (Eff ef es) x ->
  (Eff ef es x -> Eff ef' es' a) ->
  r
elabWriter return start (Tell w) next = return (start <> w) $ next $ pure ()
elabWriter return start (Listen action) next =
  return start $ next do
    (w, a) <- interposeWriter mempty action
    send $ Tell w
    pure (w, a)
elabWriter return start (Pass action) next =
  return start $ next do
    (w, (f, a)) <- interposeWriter mempty action
    send $ Tell $ f w
    pure a
