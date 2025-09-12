module PlutusTx.Plugin.Lib where

import PlutusTx.Builtins
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.List

-- This is mainly for plugin to generate code for. Always prefer using 'PlutusTx.Builtin.caseDataConstr'.
caseDataConstr' :: forall r. BuiltinData -> [[BuiltinData] -> r] -> r
caseDataConstr' d branches =
  let
    constr = BI.unsafeDataAsConstr d
    idx = BI.fst constr
    ds = BI.snd constr
    -- Use of 'fromOpaque' is EVIL. It is a necessary evil since we need
    -- slower SOP list for the plugin to match list directly for builtin-case
    -- version of this function.
  in (branches !! idx) (fromOpaque ds)
{-# INLINE caseDataConstr' #-}
