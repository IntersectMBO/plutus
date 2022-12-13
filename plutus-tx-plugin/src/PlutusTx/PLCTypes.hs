module PlutusTx.PLCTypes where

import PlutusCore qualified as PLC
import PlutusCore.MkPlc qualified as PLC
import PlutusTx.Annotation
import PlutusTx.Code
import UntypedPlutusCore qualified as UPLC

type PLCKind = PLC.Kind Ann
type PLCType uni = PLC.Type PLC.TyName uni Ann
type PLCTerm uni fun = PLC.Term PLC.TyName PLC.Name uni fun Ann
type PLCProgram uni fun = PLC.Program PLC.TyName PLC.Name uni fun ()

type PLCVar uni = PLC.VarDecl PLC.TyName PLC.Name uni Ann
type PLCTyVar = PLC.TyVarDecl PLC.TyName Ann

type UPLCProgram uni fun = UPLC.Program UPLC.NamedDeBruijn uni fun ()
type UPLCProgramDebug uni fun = UPLC.Program UPLC.NamedDeBruijn uni fun SrcSpans
