module Language.Plutus.CoreToPLC.PLCTypes where

import qualified Language.PlutusCore as PLC

type PLCKind = PLC.Kind ()
type PLCType = PLC.Type PLC.TyName ()
type PLCTerm = PLC.Term PLC.TyName PLC.Name ()

type PLCTyVar = (PLC.TyName (), PLCKind)
type PLCVar = (PLC.Name (), PLCType)
