{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.Plutus.CoreToPLC.Utils where

import qualified Language.PlutusCore as PLC
import qualified Language.PlutusIR   as PIR

import           GHC.Natural

instSize :: Natural -> PIR.Term tyname name () -> PIR.Term tyname name ()
instSize n t = PIR.TyInst () t (PLC.TyInt () n)

appSize :: Natural -> PIR.Type tyname () -> PIR.Type tyname ()
appSize n t = PIR.TyApp () t (PLC.TyInt () n)

mkConstant :: PLC.BuiltinName -> PIR.Term tyname name ()
mkConstant n = PIR.Constant () $ PLC.BuiltinName () n

mkIntFun :: PLC.BuiltinName -> PIR.Term PIR.TyName PIR.Name ()
mkIntFun name = instSize haskellIntSize (mkConstant name)

haskellIntSize :: Natural
haskellIntSize = 64

-- This is mostly so they are compatible with the output of the SHA functions
haskellBSSize :: Natural
haskellBSSize = 256

mustBeReplaced :: a
mustBeReplaced = error "This must be replaced by the core-to-plc plugin during compilation"
