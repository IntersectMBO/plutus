-- | Functions for working with PLC builtins.
module Language.Plutus.CoreToPLC.Builtins where

import           GHC.Natural
import qualified Language.PlutusCore as PLC

haskellIntSize :: Natural
haskellIntSize = 64

haskellBSSize :: Natural
haskellBSSize = 64

instSize :: Natural -> PLC.Term tyname name () -> PLC.Term tyname name ()
instSize n t = PLC.TyInst () t (PLC.TyInt () n)

appSize :: Natural -> PLC.Type tyname () -> PLC.Type tyname ()
appSize n t = PLC.TyApp () t (PLC.TyInt () n)

mkConstant :: PLC.BuiltinName -> PLC.Term tyname name ()
mkConstant n = PLC.Constant () $ PLC.BuiltinName () n

mkIntFun :: PLC.BuiltinName -> PLC.Term PLC.TyName PLC.Name ()
mkIntFun name = instSize haskellIntSize (mkConstant name)

mkIntRel :: PLC.BuiltinName -> PLC.Term PLC.TyName PLC.Name ()
mkIntRel name = instSize haskellIntSize (mkConstant name)

mkBsRel :: PLC.BuiltinName -> PLC.Term PLC.TyName PLC.Name ()
mkBsRel name = instSize haskellBSSize (mkConstant name)
