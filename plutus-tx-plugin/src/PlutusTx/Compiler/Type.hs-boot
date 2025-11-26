{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}

module PlutusTx.Compiler.Type where

import PlutusTx.Compiler.Types
import PlutusTx.PIRTypes

import GHC.Plugins qualified as GHC

compileTypeNorm :: CompilingDefault uni fun m ann => GHC.Type -> m (PIRType uni)
compileType :: CompilingDefault uni fun m ann => GHC.Type -> m (PIRType uni)
getMatchInstantiated :: CompilingDefault uni fun m ann => GHC.Type -> m (PIRTerm uni fun -> PIRType uni -> [PIRTerm uni fun] -> PIRTerm uni fun)
