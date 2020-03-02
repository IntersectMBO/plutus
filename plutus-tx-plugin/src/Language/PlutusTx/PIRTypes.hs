module Language.PlutusTx.PIRTypes where

import qualified Language.PlutusIR as PIR

type PIRKind = PIR.Kind ()
type PIRType uni = PIR.Type PIR.TyName uni ()
type PIRTerm uni = PIR.Term PIR.TyName PIR.Name uni ()
type PIRProgram uni = PIR.Program PIR.TyName PIR.Name uni ()

type PIRBinding uni = PIR.Binding PIR.TyName PIR.Name uni ()

type PIRVar uni = PIR.VarDecl PIR.TyName PIR.Name uni ()
type PIRTyVar = PIR.TyVarDecl PIR.TyName ()
