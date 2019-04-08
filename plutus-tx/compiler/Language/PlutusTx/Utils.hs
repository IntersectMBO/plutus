{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.PlutusTx.Utils where

import qualified Language.PlutusCore as PLC
import qualified Language.PlutusIR   as PIR

import           GHC.Natural

instSize :: Natural -> PIR.Term tyname name () -> PIR.Term tyname name ()
instSize n t = PIR.TyInst () t (PLC.TyInt () n)

appSize :: Natural -> PIR.Type tyname () -> PIR.Type tyname ()
appSize n t = PIR.TyApp () t (PLC.TyInt () n)

mkBuiltin :: PLC.BuiltinName -> PIR.Term tyname name ()
mkBuiltin n = PIR.Builtin () $ PLC.BuiltinName () n

mkDynBuiltin :: PLC.DynamicBuiltinName -> PIR.Term tyname name ()
mkDynBuiltin n = PIR.Builtin () $ PLC.DynBuiltinName () n

mkIntFun :: PLC.BuiltinName -> PIR.Term PIR.TyName PIR.Name ()
mkIntFun name = instSize haskellIntSize (mkBuiltin name)

-- | The size of Haskell integers as a PLC size. Sizes are in bytes, so 8 bytes is 64 bits.
haskellIntSize :: Natural
haskellIntSize = 8

-- | The size of Haskell bytestrings as a PLC size. Sizes are in bytes, so 32 bytes is 256 bits.
-- This is mostly so they are compatible with the output of the SHA functions.
haskellBS32Size :: Natural
haskellBS32Size = 32

-- | Signatures are 64 bytes long
haskellBS64Size :: Natural
haskellBS64Size = 64

mustBeReplaced :: a
mustBeReplaced = error "This must be replaced by the core-to-plc plugin during compilation"
