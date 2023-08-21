module PlutusTx.PIRTypes where

import PlutusCore.Annotation
import PlutusIR qualified as PIR

type PIRKind = PIR.Kind Ann
type PIRType uni = PIR.Type PIR.TyName uni Ann
type PIRTerm uni fun = PIR.Term PIR.TyName PIR.Name uni fun Ann
type PIRProgram uni fun = PIR.Program PIR.TyName PIR.Name uni fun SrcSpans

type PIRBinding uni fun = PIR.Binding PIR.TyName PIR.Name uni fun Ann

type PIRVar uni = PIR.VarDecl PIR.TyName PIR.Name uni Ann
type PIRTyVar = PIR.TyVarDecl PIR.TyName Ann
