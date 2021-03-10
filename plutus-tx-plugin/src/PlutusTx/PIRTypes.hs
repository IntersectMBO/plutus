module Language.PlutusTx.PIRTypes where

import qualified Language.PlutusIR as PIR

type PIRKind = PIR.Kind ()
type PIRType uni = PIR.Type PIR.TyName uni ()
type PIRTerm uni fun = PIR.Term PIR.TyName PIR.Name uni fun ()
type PIRProgram uni fun = PIR.Program PIR.TyName PIR.Name uni fun ()

type PIRBinding uni fun = PIR.Binding PIR.TyName PIR.Name uni fun ()

type PIRVar uni fun = PIR.VarDecl PIR.TyName PIR.Name uni fun ()
type PIRTyVar = PIR.TyVarDecl PIR.TyName ()
