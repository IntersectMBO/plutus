module Language.Plutus.CoreToPLC.PIRTypes where

import qualified Language.PlutusIR as PIR

type PIRKind = PIR.Kind ()
type PIRType = PIR.Type PIR.TyName ()
type PIRTerm = PIR.Term PIR.TyName PIR.Name ()
type PIRProgram = PIR.Program PIR.TyName PIR.Name ()

type PIRBinding = PIR.Binding PIR.TyName PIR.Name ()

type PIRVar = PIR.VarDecl PIR.TyName PIR.Name ()
type PIRTyVar = PIR.TyVarDecl PIR.TyName ()
