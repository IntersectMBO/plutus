{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell  #-}
module Language.PlutusIR.Compiler.Types where

import qualified Language.PlutusIR                     as PIR
import           Language.PlutusIR.Compiler.Error
import           Language.PlutusIR.Compiler.Provenance

import           Control.Monad.Except
import           Control.Monad.Reader

import           Control.Lens

import qualified Language.PlutusCore                   as PLC
import qualified Language.PlutusCore.MkPlc             as PLC
import           Language.PlutusCore.Quote
import qualified Language.PlutusCore.StdLib.Type       as Types

newtype CompilationOpts = CompilationOpts {
    _coOptimize :: Bool
    } deriving (Eq, Show)

makeLenses ''CompilationOpts

defaultCompilationOpts :: CompilationOpts
defaultCompilationOpts = CompilationOpts True

data CompilationCtx a = CompilationCtx {
    _ccOpts        :: CompilationOpts
    , _ccEnclosing :: Provenance a
    } deriving (Eq, Show)

makeLenses ''CompilationCtx

defaultCompilationCtx :: CompilationCtx a
defaultCompilationCtx = CompilationCtx defaultCompilationOpts NoProvenance

getEnclosing :: MonadReader (CompilationCtx a) m => m (Provenance a)
getEnclosing = view ccEnclosing

withEnclosing :: MonadReader (CompilationCtx a) m => (Provenance a -> Provenance a) -> m b -> m b
withEnclosing f = local (over ccEnclosing f)

runIfOpts :: MonadReader (CompilationCtx a) m => (b -> m b) -> (b -> m b)
runIfOpts pass arg = do
    doOpt <- view (ccOpts . coOptimize)
    if doOpt then pass arg else pure arg

type PLCTerm a = PLC.Term PLC.TyName PLC.Name (Provenance a)
type PLCType a = PLC.Type PLC.TyName (Provenance a)

-- | A possibly recursive type.
data PLCRecType a = PlainType (PLCType a) | RecursiveType (Types.RecursiveType (Provenance a))

-- | Get the actual type inside a 'PLCRecType'.
getType :: PLCRecType a -> PLCType a
getType r = case r of
    PlainType t                                                -> t
    RecursiveType Types.RecursiveType {Types._recursiveType=t} -> t

-- | Wrap a term appropriately for a possibly recursive type.
wrap :: Provenance a -> PLCRecType a -> [PLCType a] -> PIRTerm a -> PIRTerm a
wrap p r tvs t = case r of
    PlainType _                                                      -> t
    RecursiveType Types.RecursiveType {Types._recursiveWrap=wrapper} -> setProvenance p $ wrapper tvs t

-- | Unwrap a term appropriately for a possibly recursive type.
unwrap :: Provenance a -> PLCRecType a -> PIRTerm a -> PIRTerm a
unwrap p r t = case r of
    PlainType _                          -> t
    RecursiveType Types.RecursiveType {} -> PIR.Unwrap p t

type PIRTerm a = PIR.Term PIR.TyName PIR.Name (Provenance a)
type PIRType a = PIR.Type PIR.TyName (Provenance a)

type Compiling m e a = (Monad m, MonadReader (CompilationCtx a) m, AsError e (Provenance a), MonadError e m, MonadQuote m)

type TermDef tyname name a = PLC.Def (PLC.VarDecl tyname name a) (PIR.Term tyname name a)
