{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
module Language.PlutusIR.Compiler.Types where

import qualified Language.PlutusIR                     as PIR
import           Language.PlutusIR.Compiler.Error
import           Language.PlutusIR.Compiler.Provenance

import           Control.Monad.Except
import           Control.Monad.Reader

import qualified Language.PlutusCore                   as PLC
import qualified Language.PlutusCore.MkPlc             as PLC
import           Language.PlutusCore.Quote

type PLCTerm a = PLC.Term PLC.TyName PLC.Name (Provenance a)
type PLCType a = PLC.Type PLC.TyName (Provenance a)

type PIRTerm a = PIR.Term PIR.TyName PIR.Name (Provenance a)
type PIRType a = PIR.Type PIR.TyName (Provenance a)

type Compiling m a = (Monad m, MonadReader (Provenance a) m, MonadError (CompError (Provenance a)) m, MonadQuote m)

type TermDef tyname name a = PLC.Def (PLC.VarDecl tyname name a) (PIR.Term tyname name a)
