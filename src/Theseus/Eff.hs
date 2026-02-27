module Theseus.Eff (
  -- Welcome to Theseus's main documentation page. If you haven't already,
  -- check out the Github page's Readme for tutorials and explanations about
  -- how Theseus works.

  -- * General Effect Machinery
  Eff (Eff, unEff),
  getFacts,
  effUn,
  matchOn,
  Facts (Facts, bounded),
  ControlFlow (..),
  CF (..),
  evalCf,
  Anything,
  Nonthing,
  Implies (..),
  Iso (..),
  IsoSome (..),
  isoSomeId,
  isoImplying,
  IsAtLeast (..),
  implying,
  transImply,
  Effect,
  Freer (Pure, Impure),
  unrestrict,
  unrestrict',
  lift,
  raise,
  raiseUnder,
  Subset (raising),
  send,
  runEff,
  Final (Final),
  runEffM,
  (:>) (getProof),
  IsMember (..),
  withProof,
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
  IdentityCf (IdentityCf, runIdentityCf),

  -- * Reexports
  Identity,
) where

import Control.Monad.Identity
import Theseus.Constraints
import Theseus.EffType
import Theseus.Interpreters
import Theseus.Union
