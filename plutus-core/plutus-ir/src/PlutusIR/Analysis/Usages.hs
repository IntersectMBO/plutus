{-# LANGUAGE FlexibleContexts #-}

-- | Functions for computing variable usage inside terms and types.
module PlutusIR.Analysis.Usages
  ( module PlutusCore.Analysis.Usages
  , termUsages
  ) where

import PlutusPrelude ((<^>))

import PlutusIR
import PlutusIR.Subst

import PlutusCore.Analysis.Usages
import PlutusCore.Name.Unique qualified as PLC

import Control.Lens
import Data.MultiSet.Lens

termUsages
  :: (PLC.HasUnique name PLC.TermUnique, PLC.HasUnique tyname PLC.TypeUnique)
  => Term tyname name uni fun a
  -> Usages
termUsages = multiSetOf (vTerm . PLC.theUnique <^> tvTerm . PLC.theUnique)
