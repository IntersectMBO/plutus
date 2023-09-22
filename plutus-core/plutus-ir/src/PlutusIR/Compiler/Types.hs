-- editorconfig-checker-disable-file
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeOperators         #-}
module PlutusIR.Compiler.Types where

import PlutusIR qualified as PIR
import PlutusIR.Compiler.Provenance
import PlutusIR.Error

import Control.Monad (when)
import Control.Monad.Except (MonadError)
import Control.Monad.Reader (MonadReader, local)

import Control.Lens

import PlutusCore qualified as PLC
import PlutusCore.Annotation
import PlutusCore.Builtin qualified as PLC
import PlutusCore.MkPlc qualified as PLC
import PlutusCore.Pretty qualified as PLC
import PlutusCore.Quote
import PlutusCore.StdLib.Type qualified as Types
import PlutusCore.TypeCheck.Internal qualified as PLC
import PlutusCore.Version qualified as PLC
import PlutusPrelude

import Control.Monad.Error.Lens (throwing)
import Data.Text qualified as T
import PlutusIR.Analysis.Builtins
import Prettyprinter (viaShow)

-- | Extra flag to be passed in the TypeCheckM Reader context,
-- to signal if the PIR expression currently being typechecked is at the top-level
-- and thus its type can escape, or nested and thus not allowed to escape.
data AllowEscape = YesEscape | NoEscape

-- | extending the plc typecheck config with AllowEscape
data PirTCConfig uni fun = PirTCConfig {
      _pirConfigTCConfig      :: PLC.TypeCheckConfig uni fun
      , _pirConfigAllowEscape :: AllowEscape
     }
makeLenses ''PirTCConfig

-- pir config has inside a plc config so it can act like it
instance PLC.HasKindCheckConfig (PirTCConfig uni fun) where
    kindCheckConfig = pirConfigTCConfig . PLC.kindCheckConfig

instance PLC.HasTypeCheckConfig (PirTCConfig uni fun) uni fun where
    typeCheckConfig = pirConfigTCConfig

-- | What style to use when encoding datatypes.
-- Generally, 'SumsOfProducts' is superior, unless you are targeting an
-- old Plutus Core language version.
--
-- See Note [Encoding of datatypes]
data DatatypeStyle = ScottEncoding | SumsOfProducts
    deriving stock (Show, Read, Eq)

instance Pretty DatatypeStyle where
  pretty = viaShow

data DatatypeCompilationOpts = DatatypeCompilationOpts
    { _dcoStyle :: DatatypeStyle
    } deriving stock (Show)

makeLenses ''DatatypeCompilationOpts

defaultDatatypeCompilationOpts :: DatatypeCompilationOpts
defaultDatatypeCompilationOpts = DatatypeCompilationOpts SumsOfProducts

data CompilationOpts a = CompilationOpts {
    _coOptimize                         :: Bool
    , _coPedantic                       :: Bool
    , _coVerbose                        :: Bool
    , _coDebug                          :: Bool
    , _coDatatypes                      :: DatatypeCompilationOpts
    -- Simplifier passes
    , _coMaxSimplifierIterations        :: Int
    , _coDoSimplifierUnwrapCancel       :: Bool
    , _coDoSimplifierCaseReduce         :: Bool
    , _coDoSimplifiercommuteFnWithConst :: Bool
    , _coDoSimplifierBeta               :: Bool
    , _coDoSimplifierInline             :: Bool
    , _coDoSimplifierKnownCon           :: Bool
    , _coDoSimplifierEvaluateBuiltins   :: Bool
    , _coDoSimplifierStrictifyBindings  :: Bool
    , _coInlineHints                    :: InlineHints PLC.Name (Provenance a)
    -- Profiling
    , _coProfile                        :: Bool
    , _coRelaxedFloatin                 :: Bool
    -- | Whether to try and preserve the logging beahviour of the program.
    , _coPreserveLogging                :: Bool
    } deriving stock (Show)

makeLenses ''CompilationOpts

defaultCompilationOpts :: CompilationOpts a
defaultCompilationOpts = CompilationOpts
  { _coOptimize = True
  , _coPedantic = False
  , _coVerbose = False
  , _coDebug = False
  , _coDatatypes = defaultDatatypeCompilationOpts
  , _coMaxSimplifierIterations = 12
  , _coDoSimplifierUnwrapCancel = True
  , _coDoSimplifierCaseReduce = True
  , _coDoSimplifiercommuteFnWithConst = True
  , _coDoSimplifierKnownCon = True
  , _coDoSimplifierBeta = True
  , _coDoSimplifierInline = True
  , _coDoSimplifierEvaluateBuiltins = True
  , _coDoSimplifierStrictifyBindings = True
  , _coInlineHints = mempty
  , _coProfile = False
  , _coRelaxedFloatin = True
  , _coPreserveLogging = False
  }

data CompilationCtx uni fun a = CompilationCtx {
    _ccOpts               :: CompilationOpts a
    , _ccEnclosing        :: Provenance a
    -- | Decide to either typecheck (passing a specific tcconfig) or not by passing 'Nothing'.
    , _ccTypeCheckConfig  :: Maybe (PirTCConfig uni fun)
    , _ccBuiltinsInfo     :: BuiltinsInfo uni fun
    , _ccBuiltinCostModel :: PLC.CostingPart uni fun
    }

makeLenses ''CompilationCtx

toDefaultCompilationCtx
    :: (Default (PLC.BuiltinSemanticsVariant fun), Default (PLC.CostingPart uni fun))
    => PLC.TypeCheckConfig uni fun
    -> CompilationCtx uni fun a
toDefaultCompilationCtx configPlc =
    CompilationCtx defaultCompilationOpts noProvenance
        (Just $ PirTCConfig configPlc YesEscape)
        def
        def

validateOpts :: Compiling m e uni fun a => PLC.Version -> m ()
validateOpts v = do
  datatypes <- view (ccOpts . coDatatypes . dcoStyle)
  when (datatypes == SumsOfProducts && v < PLC.plcVersion110) $ throwing _OptionsError $ T.pack $ "Cannot use sums-of-products to compile a program with version less than 1.10. Program version is:" ++ show v

getEnclosing :: MonadReader (CompilationCtx uni fun a) m => m (Provenance a)
getEnclosing = view ccEnclosing

withEnclosing :: MonadReader (CompilationCtx uni fun a) m => (Provenance a -> Provenance a) -> m b -> m b
withEnclosing f = local (over ccEnclosing f)

runIf
  :: MonadReader (CompilationCtx uni fun a) m
  => m Bool
  -> (b -> m b)
  -> (b -> m b)
runIf condition pass arg = do
  doPass <- condition
  if doPass then pass arg else pure arg

runIfOpts :: MonadReader (CompilationCtx uni fun a) m => (b -> m b) -> (b -> m b)
runIfOpts = runIf $ view (ccOpts . coOptimize)

type PLCProgram uni fun a = PLC.Program PLC.TyName PLC.Name uni fun (Provenance a)
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
    , PLC.Typecheckable uni fun
    , PLC.GEq uni
    -- Pretty printing instances
    , PLC.PrettyUni uni
    , PLC.Pretty fun
    , PLC.Pretty a
    )

type TermDef tyname name uni fun a = PLC.Def (PLC.VarDecl tyname name uni a) (PIR.Term tyname name uni fun a)

-- | We generate some shared definitions compilation, this datatype
-- defines the "keys" for those definitions.
data SharedName =
    FixpointCombinator Integer
    | FixBy
    deriving stock (Show, Eq, Ord)

toProgramName :: SharedName -> Quote PLC.Name
toProgramName (FixpointCombinator n) = freshName ("fix" <> T.pack (show n))
toProgramName FixBy                  = freshName "fixBy"
