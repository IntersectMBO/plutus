module Language.Plutus.CoreToPLC.PLCTypes where

import qualified Language.PlutusCore       as PLC
import qualified Language.PlutusCore.MkPlc as PLC

type PLCKind = PLC.Kind ()
type PLCType = PLC.Type PLC.TyName ()
type PLCTerm = PLC.Term PLC.TyName PLC.Name ()

type PLCVar = PLC.VarDecl PLC.TyName PLC.Name ()
type PLCTyVar = PLC.TyVarDecl PLC.TyName ()
