module Language.Plutus.CoreToPLC.PLCTypes where

import qualified Language.PlutusCore as PLC

type PLCKind = PLC.Kind ()
type PLCType = PLC.Type PLC.TyName ()
type PLCTerm = PLC.Term PLC.TyName PLC.Name ()

data PLCTyVar = PLCTyVar (PLC.TyName ()) PLCKind

splitTyVar :: PLCTyVar -> (PLC.TyName (), PLCKind)
splitTyVar (PLCTyVar n k) = (n, k)

data PLCVar = PLCVar (PLC.Name ()) PLCType

splitVar :: PLCVar -> (PLC.Name (), PLCType)
splitVar (PLCVar n ty) = (n, ty)
