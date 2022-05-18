module PlutusTx.PLCTypes where

import PlutusCore qualified as PLC
import PlutusCore.MkPlc qualified as PLC
import PlutusTx.Annotation
import UntypedPlutusCore qualified as UPLC

type PLCKind = PLC.Kind Ann
type PLCType uni = PLC.Type PLC.TyName uni Ann
type PLCTerm uni fun = PLC.Term PLC.TyName PLC.Name uni fun Ann
type PLCProgram uni fun = PLC.Program PLC.TyName PLC.Name uni fun ()

type PLCVar uni fun = PLC.VarDecl PLC.TyName PLC.Name uni fun Ann
type PLCTyVar = PLC.TyVarDecl PLC.TyName Ann

type UPLCProgram uni fun = UPLC.Program UPLC.NamedDeBruijn uni fun ()
