-- editorconfig-checker-disable-file
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeOperators         #-}
module PlutusIR.Compiler.Types where


import Control.Lens
import Control.Monad (when)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.Reader (MonadReader, local)
import Data.Default.Class
import Data.Text qualified as T
import Prettyprinter (viaShow)

import PlutusCore qualified as PLC
import PlutusCore.Annotation
import PlutusCore.Builtin qualified as PLC
import PlutusCore.MkPlc qualified as PLC
import PlutusCore.Pretty qualified as PLC
import PlutusCore.Quote
import PlutusCore.AstSize (AstSize)
import PlutusCore.StdLib.Type qualified as Types
import PlutusCore.TypeCheck.Internal qualified as PLC
import PlutusCore.Version qualified as PLC
import PlutusIR qualified as PIR
import PlutusIR.Analysis.Builtins
import PlutusIR.Compiler.Provenance
import PlutusIR.Error
import PlutusIR.Transform.RewriteRules.Internal (RewriteRules)
import PlutusPrelude

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
data DatatypeStyle
    = ScottEncoding
    | SumsOfProducts
    | BuiltinCasing
      -- ^ A temporary data type style used to make a couple of V3 ledger-api-test tests pass
      -- before we can support casing on values of built-in types in newer protocol versions and
      -- merge this into 'SumsOfProducts' (which is what controls whether 'Case' is available or
      -- not).
    deriving stock (Show, Read, Eq)

instance Pretty DatatypeStyle where
  pretty = viaShow

newtype DatatypeCompilationOpts = DatatypeCompilationOpts
    { _dcoStyle :: DatatypeStyle
    } deriving newtype (Show, Read, Pretty)

makeLenses ''DatatypeCompilationOpts

defaultDatatypeCompilationOpts :: DatatypeCompilationOpts
defaultDatatypeCompilationOpts = DatatypeCompilationOpts SumsOfProducts

data CompilationOpts a = CompilationOpts {
    _coOptimize                         :: Bool
    , _coTypecheck                      :: Bool
    , _coPedantic                       :: Bool
    , _coVerbose                        :: Bool
    , _coDebug                          :: Bool
    , _coDatatypes                      :: DatatypeCompilationOpts
    -- Simplifier passes
    , _coMaxSimplifierIterations        :: Int
    , _coDoSimplifierUnwrapCancel       :: Bool
    , _coDoSimplifierCaseReduce         :: Bool
    , _coDoSimplifierRewrite            :: Bool
    , _coDoSimplifierBeta               :: Bool
    , _coDoSimplifierInline             :: Bool
    , _coDoSimplifierKnownCon           :: Bool
    , _coDoSimplifierCaseOfCase         :: Bool
    , _coDoSimplifierEvaluateBuiltins   :: Bool
    , _coDoSimplifierStrictifyBindings  :: Bool
    , _coDoSimplifierRemoveDeadBindings :: Bool
    , _coInlineHints                    :: InlineHints PLC.Name (Provenance a)
    , _coInlineConstants                :: Bool
    , _coInlineFix                      :: Bool
    , _coInlineCallsiteGrowth           :: AstSize
    -- Profiling
    , _coProfile                        :: Bool
    , _coRelaxedFloatin                 :: Bool
    , _coCaseOfCaseConservative         :: Bool
    -- | Whether to try and preserve the logging beahviour of the program.
    , _coPreserveLogging                :: Bool
    } deriving stock (Show)

makeLenses ''CompilationOpts

defaultCompilationOpts :: CompilationOpts a
defaultCompilationOpts = CompilationOpts
  { _coOptimize = True -- synonymous with max-simplifier-iterations=0
  , _coTypecheck = True
  , _coPedantic = False
  , _coVerbose = False
  , _coDebug = False
  , _coDatatypes = defaultDatatypeCompilationOpts
  , _coMaxSimplifierIterations = 12
  , _coDoSimplifierUnwrapCancel = True
  , _coDoSimplifierCaseReduce = True
  , _coDoSimplifierRewrite = True
  , _coDoSimplifierKnownCon = True
  , _coDoSimplifierCaseOfCase = True
  , _coDoSimplifierBeta = True
  , _coDoSimplifierInline = True
  , _coDoSimplifierEvaluateBuiltins = True
  , _coDoSimplifierStrictifyBindings = True
  , _coInlineHints = def
  , _coInlineConstants = True
  , _coInlineFix = True
  , _coInlineCallsiteGrowth = 5
  , _coProfile = False
  , _coRelaxedFloatin = True
  , _coCaseOfCaseConservative = True
  , _coPreserveLogging = False
  , _coDoSimplifierRemoveDeadBindings = True
  }

data CompilationCtx uni fun a = CompilationCtx {
    _ccOpts               :: CompilationOpts a
    , _ccEnclosing        :: Provenance a
    -- | Decide to either typecheck (passing a specific tcconfig) or not by passing 'Nothing'.
    , _ccTypeCheckConfig  :: PirTCConfig uni fun
    , _ccBuiltinsInfo     :: BuiltinsInfo uni fun
    , _ccBuiltinCostModel :: PLC.CostingPart uni fun
    , _ccRewriteRules     :: RewriteRules uni fun
    }

makeLenses ''CompilationCtx

toDefaultCompilationCtx
    :: (Default (BuiltinsInfo uni fun), Default (PLC.CostingPart uni fun), Default (RewriteRules uni fun))
    => PLC.TypeCheckConfig uni fun
    -> CompilationCtx uni fun a
toDefaultCompilationCtx configPlc = CompilationCtx
       { _ccOpts = defaultCompilationOpts
       , _ccEnclosing = noProvenance
       , _ccTypeCheckConfig = PirTCConfig configPlc YesEscape
       , _ccBuiltinsInfo = def
       , _ccBuiltinCostModel = def
       , _ccRewriteRules = def
       }

validateOpts :: Compiling m uni fun a => PLC.Version -> m ()
validateOpts v = do
  datatypes <- view (ccOpts . coDatatypes . dcoStyle)
  when ((datatypes == SumsOfProducts || datatypes == BuiltinCasing) && v < PLC.plcVersion110) $
    throwError $ OptionsError $ T.pack $ "Cannot use sums-of-products to compile a program with version less than 1.10. Program version is:" ++ show v

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

type Compiling m uni fun a =
    ( Monad m
    , MonadReader (CompilationCtx uni fun a) m
    , MonadError (Error uni fun (Provenance a)) m
    , PLC.AnnotateCaseBuiltin uni
    , PLC.CaseBuiltin uni
    , MonadQuote m
    , Ord a
    , AnnInline a
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
