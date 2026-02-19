-- editorconfig-checker-disable-file
{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

module PlutusTx.Options where

import PlutusCore.Error as PLC
import PlutusCore.Parser as PLC
import PlutusCore.Quote as PLC
import PlutusCore.Version qualified as PLC
import PlutusIR.Compiler qualified as PIR
import PlutusIR.Compiler.Types qualified as PIR
import PlutusTx.Compiler.Types
import UntypedPlutusCore qualified as UPLC

import Control.Exception
import Control.Lens
import Data.Bifunctor (first)
import Data.Coerce (coerce)
import Data.Either.Validation
#if __GLASGOW_HASKELL__ >= 912
import Data.Foldable (toList)
#else 
import Data.Foldable (foldl', toList)
#endif 
import Control.Applicative (many, optional, (<|>))
import Data.List qualified as List
import Data.List.NonEmpty (NonEmpty)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Proxy
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Type.Equality
import GHC.Plugins qualified as GHC
import Prettyprinter
import Text.Megaparsec.Char (alphaNumChar, char, upperChar)
import Text.Read (readMaybe)
import Type.Reflection

data PluginOptions = PluginOptions
  { _posPlcTargetVersion :: PLC.Version
  , _posDoTypecheck :: Bool
  , _posDeferErrors :: Bool
  , _posConservativeOpts :: Bool
  , _posContextLevel :: Int
  , _posDumpPir :: Bool
  , _posDumpPlc :: Bool
  , _posDumpUPlc :: Bool
  , _posOptimize :: Bool
  , _posPedantic :: Bool
  , _posVerbosity :: Verbosity
  , _posDatatypes :: PIR.DatatypeCompilationOpts
  , _posMaxSimplifierIterationsPir :: Int
  , _posMaxSimplifierIterationsUPlc :: Int
  , _posMaxCseIterations :: Int
  , _posDoSimplifierUnwrapCancel :: Bool
  , _posDoSimplifierBeta :: Bool
  , _posDoSimplifierInline :: Bool
  , _posDoSimplifierEvaluateBuiltins :: Bool
  , _posDoSimplifierStrictifyBindings :: Bool
  , _posDoSimplifierRemoveDeadBindings :: Bool
  , _posProfile :: ProfileOpts
  , _posCoverageAll :: Bool
  , _posCoverageLocation :: Bool
  , _posCoverageBoolean :: Bool
  , _posRelaxedFloatin :: Bool
  , _posCaseOfCaseConservative :: Bool
  , _posInlineCallsiteGrowth :: Int
  , _posInlineConstants :: Bool
  , _posInlineFix :: Bool
  , _posCseWhichSubterms :: UPLC.CseWhichSubterms
  , _posPreserveLogging :: Bool
  -- ^ Whether to try and retain the logging behaviour of the program.
  , -- Setting to `True` defines `trace` as `\_ a -> a` instead of the builtin version.
    -- Which effectively ignores the trace text.
    _posRemoveTrace :: Bool
  , _posDumpCompilationTrace :: Bool
  , _posCertify :: Maybe String
  }

makeLenses ''PluginOptions

type OptionKey = Text
type OptionValue = Text

-- | A data type representing option @a@ implying option @b@.
data Implication a = forall b. Implication (a -> Bool) (Lens' PluginOptions b) b

-- | A plugin option definition for a `PluginOptions` field of type @a@.
data PluginOption
  = forall a.
  Pretty a =>
  PluginOption
  { poTypeRep :: TypeRep a
  -- ^ `TypeRep` used for pretty printing the option.
  , poFun :: Maybe OptionValue -> Validation ParseError (a -> a)
  -- ^ Consumes an optional value, and either updates the field or reports an error.
  , poLens :: Lens' PluginOptions a
  {-^ Lens focusing on the field. This is for modifying the field, as well as
  getting the field value from `defaultPluginOptions` for pretty printing. -}
  , poDescription :: Text
  -- ^ A description of the option.
  , poImplications :: [Implication a]
  {-^ Implications of this option being set to a particular value.
  An option should not imply itself. -}
  }

data ParseError
  = CannotParseValue !OptionKey !OptionValue !SomeTypeRep
  | UnexpectedValue !OptionKey !OptionValue
  | MissingValue !OptionKey
  | UnrecognisedOption !OptionKey ![OptionKey]
  deriving stock (Show)

newtype ParseErrors = ParseErrors (NonEmpty ParseError)
  deriving newtype (Semigroup)

instance Show ParseErrors where
  show (ParseErrors errs) =
    "PlutusTx.Plugin: failed to parse options:\n"
      <> Text.unpack (Text.intercalate "\n" (fmap renderParseError (toList errs)))

instance Exception ParseErrors

renderParseError :: ParseError -> Text
renderParseError = \case
  CannotParseValue k v tr ->
    "Cannot parse value "
      <> Text.pack (show v)
      <> " for option "
      <> Text.pack (show k)
      <> " into type "
      <> Text.pack (show tr)
  UnexpectedValue k v ->
    "Option "
      <> Text.pack (show k)
      <> " is a flag and does not take a value, but was given "
      <> Text.pack (show v)
  MissingValue k ->
    "Option " <> Text.pack (show k) <> " needs a value"
  UnrecognisedOption k suggs ->
    "Unrecognised option: " <> Text.pack (show k) <> "." <> case suggs of
      [] -> ""
      _ -> "\nDid you mean one of:\n" <> Text.intercalate "\n" suggs

-- | Definition of plugin options.
pluginOptions :: Map OptionKey PluginOption
pluginOptions =
  Map.fromList
    [ let k = "target-version"
          desc = "The target Plutus Core language version"
       in (k, PluginOption typeRep (plcParserOption PLC.version k) posPlcTargetVersion desc [])
    , let k = "typecheck"
          desc = "Perform type checking during compilation."
       in (k, PluginOption typeRep (setTrue k) posDoTypecheck desc [])
    , let k = "defer-errors"
          desc =
            "If a compilation error happens and this option is turned on, "
              <> "the compilation error is suppressed and the original Haskell "
              <> "expression is replaced with a runtime-error expression."
       in (k, PluginOption typeRep (setTrue k) posDeferErrors desc [])
    , let k = "conservative-optimisation"
          desc =
            "When conservative optimisation is used, only the optimisations that "
              <> "never make the program worse (in terms of cost or size) are employed. "
              <> "Implies `no-relaxed-float-in`, `no-inline-constants`, `no-inline-fix`, "
              <> "`no-simplifier-evaluate-builtins`, and `preserve-logging`."
       in ( k
          , PluginOption
              typeRep
              (setTrue k)
              posConservativeOpts
              desc
              -- conservative-optimisation implies no-relaxed-floatin, and vice versa
              -- similarly, it implies preserving logging
              [ Implication (== True) posRelaxedFloatin False
              , Implication (== True) posPreserveLogging True
              , Implication (== True) posCaseOfCaseConservative True
              , Implication (== True) posInlineConstants False
              , Implication (== True) posInlineFix False
              , Implication (== True) posDoSimplifierEvaluateBuiltins False
              , Implication (== False) posRelaxedFloatin True
              , Implication (== False) posPreserveLogging False
              , Implication (== False) posCaseOfCaseConservative False
              , Implication (== False) posInlineConstants True
              , Implication (== False) posInlineFix True
              , Implication (== False) posDoSimplifierEvaluateBuiltins True
              ]
          )
    , let k = "context-level"
          desc = "Set context level for error messages."
       in (k, PluginOption typeRep (readOption k) posContextLevel desc [])
    , let k = "dump-pir"
          desc = "Dump Plutus IR"
       in (k, PluginOption typeRep (setTrue k) posDumpPir desc [])
    , let k = "dump-tplc"
          desc = "Dump Typed Plutus Core"
       in (k, PluginOption typeRep (setTrue k) posDumpPlc desc [])
    , let k = "dump-uplc"
          desc = "Dump Untyped Plutus Core"
       in (k, PluginOption typeRep (setTrue k) posDumpUPlc desc [])
    , let k = "inline-callsite-growth"
          desc =
            "Sets the inlining threshold for callsites. 0 disables inlining a binding at a "
              <> "callsite if it increases the AST size; `n` allows inlining if the AST size grows by "
              <> "no more than `n`. Keep in mind that doing so does not mean the final program "
              <> "will be bigger, since inlining can often unlock further optimizations."
       in (k, PluginOption typeRep (readOption k) posInlineCallsiteGrowth desc [])
    , let k = "inline-constants"
          desc =
            "Always inline constants. Inlining constants always reduces script "
              <> "costs slightly, but may increase script sizes if a large constant "
              <> "is used more than once. Implied by `no-conservative-optimisation`."
       in (k, PluginOption typeRep (setTrue k) posInlineConstants desc [])
    , let k = "inline-fix"
          desc =
            "Always inline fixed point combinators. This is generally preferable as "
              <> "it often enables further optimization, though it may increase script size."
       in (k, PluginOption typeRep (setTrue k) posInlineFix desc [])
    , let k = "optimize"
          desc = "Run optimization passes such as simplification and floating let-bindings."
       in (k, PluginOption typeRep (setTrue k) posOptimize desc [])
    , let k = "pedantic"
          desc = "Run type checker after each compilation pass"
       in (k, PluginOption typeRep (setTrue k) posPedantic desc [])
    , let k = "verbosity"
          desc = "Set logging verbosity level (0=Quiet, 1=Verbose, 2=Debug)"
          toVerbosity v
            | v <= 0 = Quiet
            | v == 1 = Verbose
            | otherwise = Debug
       in ( k
          , PluginOption
              typeRep
              (fromReadOption @Int k (Success . toVerbosity))
              posVerbosity
              desc
              []
          )
    , let k = "datatypes"
          desc = "Set datatype encoding style"
       in ( k
          , PluginOption
              typeRep
              (coerce <$> readOption @PIR.DatatypeStyle k)
              posDatatypes
              desc
              []
          )
    , let k = "max-simplifier-iterations-pir"
          desc = "Set the max iterations for the PIR simplifier"
       in (k, PluginOption typeRep (readOption k) posMaxSimplifierIterationsPir desc [])
    , let k = "max-simplifier-iterations-uplc"
          desc = "Set the max iterations for the UPLC simplifier"
       in (k, PluginOption typeRep (readOption k) posMaxSimplifierIterationsUPlc desc [])
    , let k = "max-cse-iterations"
          desc = "Set the max iterations for CSE"
       in (k, PluginOption typeRep (readOption k) posMaxCseIterations desc [])
    , let k = "cse-which-subterms"
          desc = "Which subterms CSE should consider (after uniquely renaming the program)"
       in (k, PluginOption typeRep (readOption k) posCseWhichSubterms desc [])
    , let k = "simplifier-unwrap-cancel"
          desc = "Run a simplification pass that cancels unwrap/wrap pairs"
       in (k, PluginOption typeRep (setTrue k) posDoSimplifierUnwrapCancel desc [])
    , let k = "simplifier-beta"
          desc = "Run a simplification pass that performs beta transformations"
       in (k, PluginOption typeRep (setTrue k) posDoSimplifierBeta desc [])
    , let k = "simplifier-evaluate-builtins"
          desc =
            "Run a simplification pass that evaluates fully saturated builtin applications. "
              <> "Implied by `no-conservative-optimisation`."
       in (k, PluginOption typeRep (setTrue k) posDoSimplifierEvaluateBuiltins desc [])
    , let k = "simplifier-inline"
          desc = "Run a simplification pass that performs inlining"
       in (k, PluginOption typeRep (setTrue k) posDoSimplifierInline desc [])
    , let k = "strictify-bindings"
          desc = "Run a simplification pass that makes bindings stricter"
       in (k, PluginOption typeRep (setTrue k) posDoSimplifierStrictifyBindings desc [])
    , let k = "simplifier-remove-dead-bindings"
          desc = "Run a simplification pass that removes dead bindings"
       in (k, PluginOption typeRep (setTrue k) posDoSimplifierRemoveDeadBindings desc [])
    , let k = "profile-all"
          desc = "Set profiling options to All, which adds tracing when entering and exiting a term."
       in (k, PluginOption typeRep (flag (const All) k) posProfile desc [])
    , let k = "coverage-all"
          desc = "Add all available coverage annotations in the trace output"
       in (k, PluginOption typeRep (setTrue k) posCoverageAll desc [])
    , let k = "coverage-location"
          desc = "Add location coverage annotations in the trace output"
       in (k, PluginOption typeRep (setTrue k) posCoverageLocation desc [])
    , let k = "coverage-boolean"
          desc = "Add boolean coverage annotations in the trace output"
       in (k, PluginOption typeRep (setTrue k) posCoverageBoolean desc [])
    , let k = "relaxed-float-in"
          desc =
            "Use a more aggressive float-in pass, which often leads to reduced costs "
              <> "but may occasionally lead to slightly increased costs. Implied by "
              <> "`no-conservative-optimisation`."
       in (k, PluginOption typeRep (setTrue k) posRelaxedFloatin desc [])
    , let k = "preserve-logging"
          desc =
            "Turn off optimisations that may alter (i.e., add, remove or change the "
              <> "order of) trace messages. Implied by `conservative-optimisation`."
       in (k, PluginOption typeRep (setTrue k) posPreserveLogging desc [])
    , let k = "remove-trace"
          desc = "Eliminate calls to `trace` from Plutus Core"
       in (k, PluginOption typeRep (setTrue k) posRemoveTrace desc [])
    , let k = "dump-compilation-trace"
          desc = "Dump compilation trace for debugging"
       in (k, PluginOption typeRep (setTrue k) posDumpCompilationTrace desc [])
    , let k = "certify"
          desc =
            "Produce a certificate for the compiled program, with the given name. "
              <> "This certificate provides evidence that the compiler optimizations have "
              <> "preserved the functional behavior of the original program. "
              <> "Currently, this is only supported for the UPLC compilation pipeline."
          p =
            optional $ do
              firstC <- upperChar
              rest <- many (alphaNumChar <|> char '_' <|> char '\\')
              pure (firstC : rest)
       in (k, PluginOption typeRep (plcParserOption p k) posCertify desc [])
    ]

flag :: (a -> a) -> OptionKey -> Maybe OptionValue -> Validation ParseError (a -> a)
flag f k = maybe (Success f) (Failure . UnexpectedValue k)

setTrue :: OptionKey -> Maybe OptionValue -> Validation ParseError (Bool -> Bool)
setTrue = flag (const True)

plcParserOption :: PLC.Parser a -> OptionKey -> Maybe OptionValue -> Validation ParseError (a -> a)
plcParserOption p k = \case
  Just t -> case PLC.runQuoteT $ PLC.parse p "none" t of
    Right v -> Success $ const v
    -- TODO: use the error
    Left (_e :: PLC.ParserErrorBundle) -> Failure $ CannotParseValue k t (someTypeRep (Proxy @Int))
  Nothing -> Failure $ MissingValue k

readOption :: Read a => OptionKey -> Maybe OptionValue -> Validation ParseError (a -> a)
readOption k = \case
  Just v
    | Just i <- readMaybe (Text.unpack v) -> Success $ const i
    | otherwise -> Failure $ CannotParseValue k v (someTypeRep (Proxy @Int))
  Nothing -> Failure $ MissingValue k

-- | Obtain an option value of type @a@ from an `Int`.
fromReadOption
  :: Read a
  => OptionKey
  -> (a -> Validation ParseError b)
  -> Maybe OptionValue
  -> Validation ParseError (b -> b)
fromReadOption k f = \case
  Just v
    | Just i <- readMaybe (Text.unpack v) -> const <$> f i
    | otherwise -> Failure $ CannotParseValue k v (someTypeRep (Proxy @Int))
  Nothing -> Failure $ MissingValue k

defaultPluginOptions :: PluginOptions
defaultPluginOptions =
  PluginOptions
    { _posPlcTargetVersion = PLC.plcVersion110
    , _posDoTypecheck = True
    , _posDeferErrors = False
    , _posConservativeOpts = False
    , _posContextLevel = 1
    , _posDumpPir = False
    , _posDumpPlc = False
    , _posDumpUPlc = False
    , _posOptimize = True
    , _posPedantic = False
    , _posVerbosity = Quiet
    , _posDatatypes = PIR.defaultDatatypeCompilationOpts
    , _posMaxSimplifierIterationsPir = view PIR.coMaxSimplifierIterations PIR.defaultCompilationOpts
    , _posMaxSimplifierIterationsUPlc = view UPLC.soMaxSimplifierIterations UPLC.defaultSimplifyOpts
    , _posMaxCseIterations = view UPLC.soMaxCseIterations UPLC.defaultSimplifyOpts
    , _posCseWhichSubterms = view UPLC.soCseWhichSubterms UPLC.defaultSimplifyOpts
    , _posDoSimplifierUnwrapCancel = True
    , _posDoSimplifierBeta = True
    , _posDoSimplifierInline = True
    , _posDoSimplifierEvaluateBuiltins = True
    , _posDoSimplifierStrictifyBindings = True
    , _posDoSimplifierRemoveDeadBindings = True
    , _posProfile = None
    , _posCoverageAll = False
    , _posCoverageLocation = False
    , _posCoverageBoolean = False
    , _posRelaxedFloatin = True
    , _posCaseOfCaseConservative = False
    , _posInlineCallsiteGrowth = 5
    , _posInlineConstants = True
    , _posInlineFix = True
    , _posPreserveLogging = True
    , _posRemoveTrace = False
    , _posDumpCompilationTrace = False
    , _posCertify = Nothing
    }

processOne
  :: OptionKey
  -> Maybe OptionValue
  -> Validation ParseError (PluginOptions -> PluginOptions)
processOne key val
  | Just (PluginOption _ f field _ impls) <- Map.lookup key pluginOptions =
      fmap (applyImplications field impls) . over field <$> f val
  -- For each boolean option there is a "no-" version for disabling it.
  | Just key' <- Text.stripPrefix "no-" key
  , Just (PluginOption tr f field _ impls) <- Map.lookup key' pluginOptions
  , Just Refl <- testEquality tr (typeRep @Bool) =
      fmap (applyImplications field impls) . over field . (not .) <$> f val
  | otherwise =
      let suggs =
            Text.pack
              <$> GHC.fuzzyMatch (Text.unpack key) (Text.unpack <$> Map.keys pluginOptions)
       in Failure (UnrecognisedOption key suggs)

applyImplications :: Lens' PluginOptions a -> [Implication a] -> PluginOptions -> PluginOptions
applyImplications field =
  foldr
    -- The value of `field` implies the value of `field'`.
    ( \(Implication f field' val) acc ->
        acc . (\opts -> if f (opts ^. field) then opts & field' .~ val else opts)
    )
    id

processAll
  :: [(OptionKey, Maybe OptionValue)]
  -> Validation ParseErrors [PluginOptions -> PluginOptions]
processAll = traverse $ first (ParseErrors . pure) . uncurry processOne

toKeyValue :: GHC.CommandLineOption -> (OptionKey, Maybe OptionValue)
toKeyValue opt = case List.elemIndex '=' opt of
  Nothing -> (Text.pack opt, Nothing)
  Just idx ->
    let (lhs, rhs) = splitAt idx opt
     in (Text.pack lhs, Just (Text.pack (drop 1 rhs)))

{-| Parses the arguments that were given to ghc at commandline as
 "-fplugin-opt PlutusTx.Plugin:opt" or "-fplugin-opt PlutusTx.Plugin:opt=val" -}
parsePluginOptions :: [GHC.CommandLineOption] -> Validation ParseErrors PluginOptions
parsePluginOptions = fmap (foldl' (flip ($)) defaultPluginOptions) . processAll . fmap toKeyValue
