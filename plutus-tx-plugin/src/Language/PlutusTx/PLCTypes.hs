module Language.PlutusTx.PLCTypes where

import qualified Language.PlutusCore       as PLC
import qualified Language.PlutusCore.MkPlc as PLC

type PLCKind = PLC.Kind ()
type PLCType uni = PLC.Type PLC.TyName uni ()
type PLCTerm uni = PLC.Term PLC.TyName PLC.Name uni ()
type PLCProgram uni = PLC.Program PLC.TyName PLC.Name uni ()

type PLCVar uni = PLC.VarDecl PLC.TyName PLC.Name uni ()
type PLCTyVar = PLC.TyVarDecl PLC.TyName ()
