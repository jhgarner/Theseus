{-# LANGUAGE QuantifiedConstraints #-}

-- Since I'm doing scary things with foralls and constraints, The "use id"
-- HLint only works when DeepSubsumption is turned on. In this module, enabling
-- DeepSubsumption causes a ton of code to stop compiling, so I'm ignoring the
-- lint.
{- HLINT ignore "Use id" -}

module Theseus.Eff (
  -- Welcome to Theseus's main documentation page. If you haven't already,
  -- check out the Github page's Readme for tutorials and explanations about
  -- how Theseus works.

  -- * General Effect Machinery
  Eff (Eff),
  ControlFlow (..),
  Anything,
  Implies (..),
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
  Member,

  -- * Handling Effects
  using,
  with,
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
import Theseus.EffType
import Theseus.Interpreters
import Theseus.Union
