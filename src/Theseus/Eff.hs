module Theseus.Eff (
  -- Welcome to Theseus's main documentation page. If you haven't already,
  -- check out the Github page's Readme for tutorials and explanations about
  -- how Theseus works.

  -- * General Effect Machinery
  Eff (Eff),
  ControlFlow (..),
  Anything,
  Implies (..),
  Iso (..),
  IsoSome (..),
  isoSomeId,
  isoImplying,
  IsAtLeast (..),
  implying,
  Effect,
  Freer (Pure, Impure),
  unrestrict,
  lift,
  raise,
  raiseUnder,
  Subset (raising),
  send,
  runEff,
  (:>),
  (:>>),

  -- * Handling Effects
  using,
  with,
  finally,
  Sender,
  Handler,
  interpret,
  Handler_,
  interpret_,
  HandlerW,
  interpretW,
  HandlerW_,
  interpretW_,
  HandlerRaw,
  interpretRaw,
  IHandlerRaw,
  interposeRaw,

  -- * Reexports
  Identity,
) where

import Control.Monad.Identity
import Theseus.Constraints
import Theseus.EffType
import Theseus.Interpreters
import Theseus.Union
