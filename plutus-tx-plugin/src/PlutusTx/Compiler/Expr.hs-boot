{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

module PlutusTx.Compiler.Expr (compileExpr, compileExprWithDefs, compileDataConRef) where

import PlutusTx.Compiler.Types
import PlutusTx.PIRTypes

import GHC.Plugins qualified as GHC

compileDataConRef :: CompilingDefault uni fun m ann => GHC.DataCon -> m (PIRTerm uni fun)
compileExpr
  :: CompilingDefault uni fun m ann
  => GHC.CoreExpr -> m (PIRTerm uni fun)
compileExprWithDefs
  :: CompilingDefault uni fun m ann
  => GHC.CoreExpr -> m (PIRTerm uni fun)
