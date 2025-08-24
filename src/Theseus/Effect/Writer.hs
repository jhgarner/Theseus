module Theseus.Effect.Writer where

import Control.Monad.Identity
import Theseus.Eff

data Writer w :: Effect where
  Tell :: w -> Writer w m ()
  Listen :: (Writer w `Member` es, ef Identity) => Eff ef es a -> Writer w (Eff ef es) (w, a)
  Pass :: (Writer w `Member` es, ef Identity) => Eff ef es (w -> w, a) -> Writer w (Eff ef es) a

tell :: Writer w `Member` es => w -> Eff ef es ()
tell w = send $ Tell w

listen :: (Writer w `Member` es, ef Identity) => Eff ef es a -> Eff ef es (w, a)
listen action = send $ Listen action

pass :: (Writer w `Member` es, ef Identity) => Eff ef es (w -> w, a) -> Eff ef es a
pass action = send $ Pass action

runWriter :: (Monoid w, ef Identity) => Eff ef (Writer w : es) a -> Eff ef es (w, a)
runWriter = runWriterFrom mempty

runWriterFrom :: (Monoid w, ef Identity) => w -> Eff ef (Writer w : es) a -> Eff ef es (w, a)
runWriterFrom w = handle (pure . (w,)) (elabWriter w)

-- Writer is currently broken and I need to fix it. Interpose is easy to use
-- incorrectly.
elabWriter :: (Monoid w, ef Identity) => w -> Handler (Writer w) ef es ((,) w)
elabWriter start (Tell w) next = runWriterFrom (start <> w) $ next $ pure ()

-- elabWriter start (Listen action) next = runWriterFrom start $ next do
--   (w, a) <- interpose (pure . (start,)) (elabWriter start) action
--   send $ Tell w
--   pure (w, a)
-- elabWriter start (Pass action) next = runWriterFrom start $ next do
--   (w, (f, a)) <- interpose (pure . (start,)) (elabWriter start) action
--   send $ Tell $ f w
--   pure a
