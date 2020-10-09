{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeOperators   #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE MultiParamTypeClasses   #-}
module Language.PlutusIR.Compiler.Types where

import qualified Language.PlutusIR                     as PIR
import           Language.PlutusIR.Error
import           Language.PlutusIR.Compiler.Provenance

import           Control.Monad.Except
import           Control.Monad.Reader

import           Control.Lens

import qualified Language.PlutusCore.TypeCheck.Internal as PLC
import qualified Language.PlutusCore                   as PLC
import qualified Language.PlutusCore.MkPlc             as PLC
import qualified Language.PlutusCore.Constant          as PLC
import           Language.PlutusCore.Quote
import qualified Language.PlutusCore.StdLib.Type       as Types

import qualified Data.Text                             as T

-- | Extra flag to be passed in the TypeCheckM Reader context,
-- to signal if the PIR expression currently being typechecked is at the top-level
-- and thus its type can escape, or nested and thus not allowed to escape.
data AllowEscape = YesEscape | NoEscape

-- | extending theh plc typecheck config with AllowEscape
data PirTCConfig uni fun = PirTCConfig {
      _pirConfigTCConfig :: PLC.TypeCheckConfig uni fun
      , _pirConfigAllowEscape :: AllowEscape
     }
makeLenses ''PirTCConfig

-- pir config has inside a plc config so it can act like it
instance PLC.HasTypeCheckConfig (PirTCConfig uni fun) uni fun where
    typeCheckConfig = pirConfigTCConfig

newtype CompilationOpts = CompilationOpts {
    _coOptimize :: Bool
    } deriving (Eq, Show)

makeLenses ''CompilationOpts

defaultCompilationOpts :: CompilationOpts
defaultCompilationOpts = CompilationOpts True

data CompilationCtx uni fun a = CompilationCtx {
    _ccOpts        :: CompilationOpts
--     , _ccBuiltinMeanings :: fun -> PLC.BuiltinMeaning (PIR.Term PLC.TyName PLC.Name uni fun ())
    , _ccEnclosing :: Provenance a
    , _ccTypeCheckConfig :: PirTCConfig uni fun
    }

makeLenses ''CompilationCtx

toDefaultCompilationCtx :: PLC.TypeCheckConfig uni fun -> CompilationCtx uni fun a
toDefaultCompilationCtx configPlc = CompilationCtx defaultCompilationOpts noProvenance (PirTCConfig configPlc YesEscape)

getEnclosing :: MonadReader (CompilationCtx uni fun a) m => m (Provenance a)
getEnclosing = view ccEnclosing

withEnclosing :: MonadReader (CompilationCtx uni fun a) m => (Provenance a -> Provenance a) -> m b -> m b
withEnclosing f = local (over ccEnclosing f)

runIfOpts :: MonadReader (CompilationCtx uni fun a) m => (b -> m b) -> (b -> m b)
runIfOpts pass arg = do
    doOpt <- view (ccOpts . coOptimize)
    if doOpt then pass arg else pure arg

type PLCTerm uni fun a = PLC.Term PLC.TyName PLC.Name uni fun (Provenance a)
type PLCType uni a = PLC.Type PLC.TyName uni (Provenance a)

-- | A possibly recursive type.
data PLCRecType uni fun a
    = PlainType (PLCType uni a)
    | RecursiveType (Types.RecursiveType uni fun (Provenance a))

-- | Get the actual type inside a 'PLCRecType'.
getType :: PLCRecType uni fun a -> PLCType uni a
getType r = case r of
    PlainType t                                                -> t
    RecursiveType Types.RecursiveType {Types._recursiveType=t} -> t

-- | Wrap a term appropriately for a possibly recursive type.
wrap :: Provenance a -> PLCRecType uni fun a -> [PLCType uni a] -> PIRTerm uni fun a -> PIRTerm uni fun a
wrap p r tvs t = case r of
    PlainType _                                                      -> t
    RecursiveType Types.RecursiveType {Types._recursiveWrap=wrapper} -> setProvenance p $ wrapper tvs t

-- | Unwrap a term appropriately for a possibly recursive type.
unwrap :: Provenance a -> PLCRecType uni fun a -> PIRTerm uni fun a -> PIRTerm uni fun a
unwrap p r t = case r of
    PlainType _                          -> t
    RecursiveType Types.RecursiveType {} -> PIR.Unwrap p t

type PIRTerm uni fun a = PIR.Term PIR.TyName PIR.Name uni fun (Provenance a)
type PIRType uni a = PIR.Type PIR.TyName uni (Provenance a)

type Compiling m e uni fun a =
    ( Monad m
    , MonadReader (CompilationCtx uni fun a) m
    , AsTypeError e (PIR.Term PIR.TyName PIR.Name uni fun ()) uni fun (Provenance a)
    , AsTypeErrorExt e uni (Provenance a)
    , AsError e uni fun (Provenance a)
    , MonadError e m
    , MonadQuote m
    , Ord a
    , PLC.GShow uni, PLC.GEq uni
    , PLC.DefaultUni PLC.<: uni
    )

type TermDef tyname name uni fun a = PLC.Def (PLC.VarDecl tyname name uni fun a) (PIR.Term tyname name uni fun a)

-- | We generate some shared definitions compilation, this datatype
-- defines the "keys" for those definitions.
data SharedName =
    FixpointCombinator Integer
    | FixBy
    deriving (Show, Eq, Ord)

toProgramName :: SharedName -> Quote PLC.Name
toProgramName (FixpointCombinator n) = freshName ("fix" <> T.pack (show n))
toProgramName FixBy                  = freshName "fixBy"
