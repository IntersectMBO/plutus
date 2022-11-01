-- editorconfig-checker-disable-file
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes       #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE StrictData        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}

module PlutusTx.Options where

import PlutusIR.Compiler qualified as PIR
import PlutusTx.Compiler.Types

import Control.Exception
import Control.Lens
import Data.Bifunctor (first)
import Data.Either.Validation
import Data.Foldable (foldl', toList)
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
import PyF (fmt)

import Text.Read (readMaybe)
import Type.Reflection

data PluginOptions = PluginOptions
    { _posDoTypecheck                    :: Bool
    , _posDeferErrors                    :: Bool
    , _posContextLevel                   :: Int
    , _posDumpPir                        :: Bool
    , _posDumpPlc                        :: Bool
    , _posDumpUPlc                       :: Bool
    , _posOptimize                       :: Bool
    , _posPedantic                       :: Bool
    , _posVerbose                        :: Bool
    , _posDebug                          :: Bool
    , _posMaxSimplifierIterations        :: Int
    , _posDoSimplifierUnwrapCancel       :: Bool
    , _posDoSimplifierBeta               :: Bool
    , _posDoSimplifierInline             :: Bool
    , _posDoSimplifierRemoveDeadBindings :: Bool
    , _posProfile                        :: ProfileOpts
    , _posCoverageAll                    :: Bool
    , _posCoverageLocation               :: Bool
    , _posCoverageBoolean                :: Bool
    , -- Setting to `True` defines `trace` as `\_ a -> a` instead of the builtin version.
      -- Which effectively ignores the trace text.
      _posRemoveTrace                    :: Bool
    }

makeLenses ''PluginOptions

type OptionKey = Text
type OptionValue = Text

-- | A plugin option definition for a `PluginOptions` field of type @a@.
data PluginOption = forall a.
      Pretty a =>
    PluginOption
    { poTypeRep     :: TypeRep a
    -- ^ `TypeRep` used for pretty printing the option.
    , poFun         :: Maybe OptionValue -> Validation ParseError (a -> a)
    -- ^ Consumes an optional value, and either updates the field or reports an error.
    , poLens        :: Lens' PluginOptions a
    -- ^ Lens focusing on the field. This is for modifying the field, as well as
    -- getting the field value from `defaultPluginOptions` for pretty printing.
    , poDescription :: Text
    -- ^ A description of the option.
    }

data ParseError
    = CannotParseValue OptionKey OptionValue SomeTypeRep
    | UnexpectedValue OptionKey OptionValue
    | MissingValue OptionKey
    | UnrecognisedOption OptionKey [OptionKey]
    deriving stock (Show)

newtype ParseErrors = ParseErrors (NonEmpty ParseError)
    deriving newtype (Semigroup)

instance Show ParseErrors where
    show (ParseErrors errs) = [fmt|
        PlutusTx.Plugin: failed to parse options:
        {Text.intercalate "\n" (fmap renderParseError (toList errs))}
    |]

instance Exception ParseErrors

renderParseError :: ParseError -> Text
renderParseError = \case
    CannotParseValue k v tr ->
        [fmt|Cannot parse value {v} for option {k} into type {show tr}.|]
    UnexpectedValue k v ->
        [fmt|Option {k} is a flag and does not take a value, but was given {v}.|]
    MissingValue k ->
        [fmt|Option {k} needs a value.|]
    UnrecognisedOption k suggs ->
        [fmt|Unrecognised option: {k}.|] <> case suggs of
            [] -> ""
            _  -> [fmt|\nDid you mean one of:\n{Text.intercalate "\n" suggs}|]

{- | Definition of plugin options.

 TODO: write a description for each option.
-}
pluginOptions :: Map OptionKey PluginOption
pluginOptions =
    Map.fromList
        [ let k = "typecheck"
              desc = "Perform type checking during compilation."
           in (k, PluginOption typeRep (setTrue k) posDoTypecheck desc)
        , let k = "defer-errors"
              desc =
                "If a compilation error happens and this option is turned on, \
                 \the compilation error is suppressed and the original Haskell \
                 \expression is replaced with a runtime-error expression."
           in (k, PluginOption typeRep (setTrue k) posDeferErrors desc)
        , let k = "no-context"
              desc = "Set context level to 0, which means error messages contain minimum contexts."
           in (k, PluginOption typeRep (flag (const 0) k) posContextLevel desc)
        , let k = "debug-context"
              desc = "Set context level to 3, which means error messages contain full contexts."
           in (k, PluginOption typeRep (flag (const 3) k) posContextLevel desc)
        , let k = "dump-pir"
              desc = "Dump Plutus IR"
           in (k, PluginOption typeRep (setTrue k) posDumpPir desc)
        , let k = "dump-plc"
              desc = "Dump Typed Plutus Core"
           in (k, PluginOption typeRep (setTrue k) posDumpPlc desc)
        , let k = "dump-uplc"
              desc = "Dump Untyped Plutus Core"
           in (k, PluginOption typeRep (setTrue k) posDumpUPlc desc)
        , let k = "optimize"
              desc = "Run optimization passes such as simplification and floating let-bindings."
           in (k, PluginOption typeRep (setTrue k) posOptimize desc)
        , let k = "pedantic"
              desc = "Run type checker after each compilation pass"
           in (k, PluginOption typeRep (setTrue k) posPedantic desc)
        , let k = "verbose"
              desc = "Set log level to verbose"
           in (k, PluginOption typeRep (setTrue k) posVerbose desc)
        , let k = "debug"
              desc = "Set log level to debug"
           in (k, PluginOption typeRep (setTrue k) posDebug desc)
        , let k = "max-simplifier-iterations"
              desc = "Set the max iterations for the simplifier"
           in (k, PluginOption typeRep (intOption k) posMaxSimplifierIterations desc)
        , let k = "simplifier-unwrap-cancel"
              desc = "Run a simplification pass that cancels unwrap/wrap pairs"
           in (k, PluginOption typeRep (setTrue k) posDoSimplifierUnwrapCancel desc)
        , let k = "simplifier-beta"
              desc = "Run a simplification pass that performs beta transformations"
           in (k, PluginOption typeRep (setTrue k) posDoSimplifierBeta desc)
        , let k = "simplifier-inline"
              desc = "Run a simplification pass that performs inlining"
           in (k, PluginOption typeRep (setTrue k) posDoSimplifierInline desc)
        , let k = "simplifier-remove-dead-bindings"
              desc = "Run a simplification pass that removes dead bindings"
           in (k, PluginOption typeRep (setTrue k) posDoSimplifierRemoveDeadBindings desc)
        , let k = "profile-all"
              desc = "Set profiling options to All, which adds tracing when entering and exiting a term."
           in (k, PluginOption typeRep (flag (const All) k) posProfile desc)
        , let k = "coverage-all"
              desc = "Add all available coverage annotations in the trace output"
           in (k, PluginOption typeRep (setTrue k) posCoverageAll desc)
        , let k = "coverage-location"
              desc = "Add location coverage annotations in the trace output"
           in (k, PluginOption typeRep (setTrue k) posCoverageLocation desc)
        , let k = "coverage-boolean"
              desc = "Add boolean coverage annotations in the trace output"
           in (k, PluginOption typeRep (setTrue k) posCoverageBoolean desc)
        , let k = "remove-trace"
              desc = "Eliminate calls to ``trace`` from Plutus Core"
           in (k, PluginOption typeRep (setTrue k) posRemoveTrace desc)
        ]

flag :: (a -> a) -> OptionKey -> Maybe OptionValue -> Validation ParseError (a -> a)
flag f k = maybe (Success f) (Failure . UnexpectedValue k)

setTrue :: OptionKey -> Maybe OptionValue -> Validation ParseError (Bool -> Bool)
setTrue = flag (const True)

intOption :: OptionKey -> Maybe OptionValue -> Validation ParseError (Int -> Int)
intOption k = \case
    Just v
        | Just i <- readMaybe (Text.unpack v) -> Success $ const i
        | otherwise -> Failure $ CannotParseValue k v (someTypeRep (Proxy @Int))
    Nothing -> Failure $ MissingValue k

defaultPluginOptions :: PluginOptions
defaultPluginOptions =
    PluginOptions
        { _posDoTypecheck = True
        , _posDeferErrors = False
        , _posContextLevel = 1
        , _posDumpPir = False
        , _posDumpPlc = False
        , _posDumpUPlc = False
        , _posOptimize = True
        , _posPedantic = False
        , _posVerbose = False
        , _posDebug = False
        , _posMaxSimplifierIterations = view PIR.coMaxSimplifierIterations PIR.defaultCompilationOpts
        , _posDoSimplifierUnwrapCancel = True
        , _posDoSimplifierBeta = True
        , _posDoSimplifierInline = True
        , _posDoSimplifierRemoveDeadBindings = True
        , _posProfile = None
        , _posCoverageAll = False
        , _posCoverageLocation = False
        , _posCoverageBoolean = False
        , _posRemoveTrace = False
        }

processOne ::
    OptionKey ->
    Maybe OptionValue ->
    Validation ParseError (PluginOptions -> PluginOptions)
processOne key val
    | Just (PluginOption _ f field _) <- Map.lookup key pluginOptions = over field <$> f val
    -- For each boolean option there is a "no-" version for disabling it.
    | Just key' <- Text.stripPrefix "no-" key
    , Just (PluginOption tr f field _) <- Map.lookup key' pluginOptions
    , Just Refl <- testEquality tr (typeRep @Bool) =
        over field . (not .) <$> f val
    | otherwise =
        let suggs =
                Text.pack
                    <$> GHC.fuzzyMatch (Text.unpack key) (Text.unpack <$> Map.keys pluginOptions)
         in Failure (UnrecognisedOption key suggs)

processAll ::
    [(OptionKey, Maybe OptionValue)] ->
    Validation ParseErrors [PluginOptions -> PluginOptions]
processAll = traverse $ first (ParseErrors . pure) . uncurry processOne

toKeyValue :: GHC.CommandLineOption -> (OptionKey, Maybe OptionValue)
toKeyValue opt = case List.elemIndex '=' opt of
    Nothing -> (Text.pack opt, Nothing)
    Just idx ->
        let (lhs, rhs) = splitAt idx opt
         in (Text.pack lhs, Just (Text.pack (drop 1 rhs)))

{- | Parses the arguments that were given to ghc at commandline as
 "-fplugin-opt PlutusTx.Plugin:opt" or "-fplugin-opt PlutusTx.Plugin:opt=val"
-}
parsePluginOptions :: [GHC.CommandLineOption] -> Validation ParseErrors PluginOptions
parsePluginOptions = fmap (foldl' (flip ($)) defaultPluginOptions) . processAll . fmap toKeyValue
