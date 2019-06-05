{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.PlutusTx.Utils where

import qualified Language.PlutusCore as PLC
import qualified Language.PlutusIR   as PIR

mkBuiltin :: PLC.BuiltinName -> PIR.Term tyname name ()
mkBuiltin n = PIR.Builtin () $ PLC.BuiltinName () n

mkDynBuiltin :: PLC.DynamicBuiltinName -> PIR.Term tyname name ()
mkDynBuiltin n = PIR.Builtin () $ PLC.DynBuiltinName () n

mustBeReplaced :: String -> a
mustBeReplaced message = error $ "This must be replaced by the core-to-plc plugin during compilation: " <> message
