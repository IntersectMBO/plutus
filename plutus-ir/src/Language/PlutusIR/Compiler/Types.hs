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
import qualified Language.PlutusCore.StdLib.Type       as Types

type PLCTerm a = PLC.Term PLC.TyName PLC.Name (Provenance a)
type PLCType a = PLC.Type PLC.TyName (Provenance a)

-- | A possibly recursive type.
data PLCRecType a = PlainType (PLCType a) | RecursiveType (Types.RecursiveType PLC.TyName (Provenance a))

-- The 'Quote' is mainly so this is forwards compatible with the ifix version.
-- | Make a 'Types.RecursiveType' for the given provenance, name, and pattern functor.
mkRecursiveType :: Provenance a -> PLC.TyName (Provenance a) -> PLCType a -> Quote (Types.RecursiveType PLC.TyName (Provenance a))
mkRecursiveType ann tn pf = pure $ Types.RecursiveType (\t -> PLC.Wrap ann tn pf t) (PLC.TyFix ann tn pf)

-- | Get the actual type inside a 'PLCRecType'.
getType :: PLCRecType a -> PLCType a
getType r = case r of
    PlainType t                                                -> t
    RecursiveType Types.RecursiveType {Types._recursiveType=t} -> t

-- | Wrap a term appropriately for a possibly recursive type.
wrap :: Provenance a -> PLCRecType a -> PLCTerm a -> PLCTerm a
wrap p r t = case r of
    PlainType _                                                      -> t
    RecursiveType Types.RecursiveType {Types._recursiveWrap=wrapper} -> setProvenance p $ wrapper t

-- | Unwrap a term appropriately for a possibly recursive type.
unwrap :: Provenance a -> PLCRecType a -> PLCTerm a -> PLCTerm a
unwrap p r t = case r of
    PlainType _                          -> t
    RecursiveType Types.RecursiveType {} -> PLC.Unwrap p t

type PIRTerm a = PIR.Term PIR.TyName PIR.Name (Provenance a)
type PIRType a = PIR.Type PIR.TyName (Provenance a)

type Compiling m e a = (Monad m, MonadReader (Provenance a) m, AsError e (Provenance a), MonadError e m, MonadQuote m)

type TermDef tyname name a = PLC.Def (PLC.VarDecl tyname name a) (PIR.Term tyname name a)
