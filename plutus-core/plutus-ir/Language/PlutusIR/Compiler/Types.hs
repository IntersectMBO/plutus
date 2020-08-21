{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeOperators   #-}
module Language.PlutusIR.Compiler.Types where

import qualified Language.PlutusIR                     as PIR
import           Language.PlutusIR.Compiler.Error
import           Language.PlutusIR.Compiler.Provenance

import           Control.Monad.Except
import           Control.Monad.Reader

import           Control.Lens

import qualified Language.PlutusCore                   as PLC
import qualified Language.PlutusCore.MkPlc             as PLC
import qualified Language.PlutusCore.Constant          as PLC
import           Language.PlutusCore.Quote
import qualified Language.PlutusCore.StdLib.Type       as Types

import qualified Data.Text                             as T

newtype CompilationOpts = CompilationOpts {
    _coOptimize :: Bool
    } deriving (Eq, Show)

makeLenses ''CompilationOpts

defaultCompilationOpts :: CompilationOpts
defaultCompilationOpts = CompilationOpts True

data CompilationCtx uni a = CompilationCtx {
    _ccOpts        :: CompilationOpts
    , _ccBuiltinMeanings :: PLC.DynamicBuiltinNameMeanings (PIR.Term PLC.TyName PLC.Name uni ())
    , _ccEnclosing :: Provenance a
    }

makeLenses ''CompilationCtx

defaultCompilationCtx :: CompilationCtx uni a
defaultCompilationCtx = CompilationCtx defaultCompilationOpts mempty noProvenance

getEnclosing :: MonadReader (CompilationCtx uni a) m => m (Provenance a)
getEnclosing = view ccEnclosing

withEnclosing :: MonadReader (CompilationCtx uni a) m => (Provenance a -> Provenance a) -> m b -> m b
withEnclosing f = local (over ccEnclosing f)

runIfOpts :: MonadReader (CompilationCtx uni a) m => (b -> m b) -> (b -> m b)
runIfOpts pass arg = do
    doOpt <- view (ccOpts . coOptimize)
    if doOpt then pass arg else pure arg

type PLCTerm uni a = PLC.Term PLC.TyName PLC.Name uni (Provenance a)
type PLCType uni a = PLC.Type PLC.TyName uni (Provenance a)

-- | A possibly recursive type.
data PLCRecType uni a
    = PlainType (PLCType uni a)
    | RecursiveType (Types.RecursiveType uni (Provenance a))

-- | Get the actual type inside a 'PLCRecType'.
getType :: PLCRecType uni a -> PLCType uni a
getType r = case r of
    PlainType t                                                -> t
    RecursiveType Types.RecursiveType {Types._recursiveType=t} -> t

-- | Wrap a term appropriately for a possibly recursive type.
wrap :: Provenance a -> PLCRecType uni a -> [PLCType uni a] -> PIRTerm uni a -> PIRTerm uni a
wrap p r tvs t = case r of
    PlainType _                                                      -> t
    RecursiveType Types.RecursiveType {Types._recursiveWrap=wrapper} -> setProvenance p $ wrapper tvs t

-- | Unwrap a term appropriately for a possibly recursive type.
unwrap :: Provenance a -> PLCRecType uni a -> PIRTerm uni a -> PIRTerm uni a
unwrap p r t = case r of
    PlainType _                          -> t
    RecursiveType Types.RecursiveType {} -> PIR.Unwrap p t

type PIRTerm uni a = PIR.Term PIR.TyName PIR.Name uni (Provenance a)
type PIRType uni a = PIR.Type PIR.TyName uni (Provenance a)

type Compiling m e uni a =
    ( Monad m
    , MonadReader (CompilationCtx uni a) m
    , AsError e uni (Provenance a)
    , MonadError e m
    , MonadQuote m
    , Ord a
    , PLC.GShow uni, PLC.GEq uni
    , PLC.DefaultUni PLC.<: uni
    )

type TermDef tyname name uni a = PLC.Def (PLC.VarDecl tyname name uni a) (PIR.Term tyname name uni a)

-- | We generate some shared definitions compilation, this datatype
-- defines the "keys" for those definitions.
data SharedName =
    FixpointCombinator Integer
    | FixBy
    deriving (Show, Eq, Ord)

toProgramName :: SharedName -> Quote PLC.Name
toProgramName (FixpointCombinator n) = freshName ("fix" <> T.pack (show n))
toProgramName FixBy                  = freshName "fixBy"
