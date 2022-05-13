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
import GhcPlugins qualified as GHC
import PyF (fmt)
import Text.Read (readMaybe)
import Type.Reflection

data PluginOptions = PluginOptions
    { _poDoTypecheck                    :: Bool
    , _poDeferErrors                    :: Bool
    , _poContextLevel                   :: Int
    , _poDumpPir                        :: Bool
    , _poDumpPlc                        :: Bool
    , _poDumpUPlc                       :: Bool
    , _poOptimize                       :: Bool
    , _poPedantic                       :: Bool
    , _poVerbose                        :: Bool
    , _poDebug                          :: Bool
    , _poMaxSimplifierIterations        :: Int
    , _poDoSimplifierUnwrapCancel       :: Bool
    , _poDoSimplifierBeta               :: Bool
    , _poDoSimplifierInline             :: Bool
    , _poDoSimplifierRemoveDeadBindings :: Bool
    , _poProfile                        :: ProfileOpts
    , _poCoverageAll                    :: Bool
    , _poCoverageLocation               :: Bool
    , _poCoverageBoolean                :: Bool
    , -- Setting to `True` defines `trace` as `\_ a -> a` instead of the builtin version.
      -- Which effectively ignores the trace text.
      _poRemoveTrace                    :: Bool
    }

makeLenses ''PluginOptions

type OptionKey = Text
type OptionValue = Text

-- | A plugin option definition for a `PluginOptions` field of type @a@.
data PluginOption
    = forall a.
        PluginOption
        (TypeRep a)
        -- ^ `TypeRep` used for pretty printing the option.
        (Maybe OptionValue -> Validation ParseError (a -> a))
        -- ^ Consumes an optional value, and either updates the field or reports an error.
        (Lens' PluginOptions a)
        -- ^ Lens focusing on the field. This is for modifying the field, as well as
        -- getting the field value from `defaultPluginOptions` for pretty printing.
        (a -> Text)
        -- ^ Display the field value.
        Text
        -- ^ A description of the option.

data ParseError
    = CannotParseValue OptionKey OptionValue SomeTypeRep
    | UnexpectedValue OptionKey OptionValue
    | MissingValue OptionKey
    | UnrecognisedOption OptionKey [OptionKey]
    deriving stock (Show)

newtype ParseErrors = ParseErrors (NonEmpty ParseError)
    deriving newtype (Semigroup)

instance Show ParseErrors where
    show (ParseErrors errs) =
        [fmt|PlutusTx.Plugin: failed to parse options:
{Text.intercalate "\n" (fmap renderParseError (toList errs))}|]

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
        [fmt|Unrecgonised option: {k}.|] <> case suggs of
            [] -> ""
            _ ->
                [fmt|
Did you mean one of:
{Text.intercalate "\n" suggs}|]

{- | Definition of plugin options.

 TODO: write a description for each option.
-}
pluginOptions :: Map OptionKey PluginOption
pluginOptions =
    Map.fromList
        [ let k = "no-typecheck"
           in (k, PluginOption typeRep (setFalse k) poDoTypecheck showText mempty)
        , let k = "defer-errors"
           in (k, PluginOption typeRep (setTrue k) poDeferErrors showText mempty)
        , let k = "no-context"
           in (k, PluginOption typeRep (flag (const 0) k) poContextLevel showText mempty)
        , let k = "debug-context"
           in (k, PluginOption typeRep (flag (const 3) k) poContextLevel showText mempty)
        , let k = "dump-pir"
           in (k, PluginOption typeRep (setTrue k) poDumpPir showText mempty)
        , let k = "dump-plc"
           in (k, PluginOption typeRep (setTrue k) poDumpPlc showText mempty)
        , let k = "dump-uplc"
           in (k, PluginOption typeRep (setTrue k) poDumpUPlc showText mempty)
        , let k = "no-optimize"
           in (k, PluginOption typeRep (setFalse k) poOptimize showText mempty)
        , let k = "pedantic"
           in (k, PluginOption typeRep (setTrue k) poPedantic showText mempty)
        , let k = "verbose"
           in (k, PluginOption typeRep (setTrue k) poVerbose showText mempty)
        , let k = "debug"
           in (k, PluginOption typeRep (setTrue k) poDebug showText mempty)
        , let k = "max-simplifier-iterations"
           in (k, PluginOption typeRep (intOption k) poMaxSimplifierIterations showText mempty)
        , let k = "no-simplifier-unwrap-cancel"
           in (k, PluginOption typeRep (setFalse k) poDoSimplifierUnwrapCancel showText mempty)
        , let k = "no-simplifier-beta"
           in (k, PluginOption typeRep (setFalse k) poDoSimplifierBeta showText mempty)
        , let k = "no-simplifier-inline"
           in (k, PluginOption typeRep (setFalse k) poDoSimplifierInline showText mempty)
        , let k = "no-simplifier-remove-dead-bindings"
           in (k, PluginOption typeRep (setFalse k) poDoSimplifierRemoveDeadBindings showText mempty)
        , let k = "profile-all"
           in (k, PluginOption typeRep (flag (const All) k) poProfile showText mempty)
        , let k = "coverage-all"
           in (k, PluginOption typeRep (setTrue k) poCoverageAll showText mempty)
        , let k = "coverage-location"
           in (k, PluginOption typeRep (setTrue k) poCoverageLocation showText mempty)
        , let k = "coverage-boolean"
           in (k, PluginOption typeRep (setTrue k) poCoverageBoolean showText mempty)
        , let k = "remove-trace"
           in (k, PluginOption typeRep (setTrue k) poRemoveTrace showText mempty)
        ]
  where
    showText :: Show a => a -> Text
    showText = Text.pack . show

flag :: (a -> a) -> OptionKey -> Maybe OptionValue -> Validation ParseError (a -> a)
flag f k = maybe (Success f) (Failure . UnexpectedValue k)

setTrue :: OptionKey -> Maybe OptionValue -> Validation ParseError (Bool -> Bool)
setTrue = flag (const True)

setFalse :: OptionKey -> Maybe OptionValue -> Validation ParseError (Bool -> Bool)
setFalse = flag (const False)

intOption :: OptionKey -> Maybe OptionValue -> Validation ParseError (Int -> Int)
intOption k = \case
    Just v ->
        maybe
            (Failure (CannotParseValue k v (someTypeRep (Proxy @Int))))
            (Success . const)
            (readMaybe (Text.unpack v))
    Nothing -> Failure (MissingValue k)

defaultPluginOptions :: PluginOptions
defaultPluginOptions =
    PluginOptions
        { _poDoTypecheck = True
        , _poDeferErrors = False
        , _poContextLevel = 1
        , _poDumpPir = False
        , _poDumpPlc = False
        , _poDumpUPlc = False
        , _poOptimize = True
        , _poPedantic = False
        , _poVerbose = False
        , _poDebug = False
        , _poMaxSimplifierIterations = view PIR.coMaxSimplifierIterations PIR.defaultCompilationOpts
        , _poDoSimplifierUnwrapCancel = True
        , _poDoSimplifierBeta = True
        , _poDoSimplifierInline = True
        , _poDoSimplifierRemoveDeadBindings = True
        , _poProfile = None
        , _poCoverageAll = False
        , _poCoverageLocation = False
        , _poCoverageBoolean = False
        , _poRemoveTrace = False
        }

processOne ::
    OptionKey ->
    Maybe OptionValue ->
    Validation ParseError (PluginOptions -> PluginOptions)
processOne key val = case Map.lookup key pluginOptions of
    Just (PluginOption _ f field _ _) -> over field <$> f val
    Nothing ->
        let suggs =
                Text.pack
                    <$> GHC.fuzzyMatch (Text.unpack key) (Text.unpack <$> Map.keys pluginOptions)
         in Failure (UnrecognisedOption key suggs)

processAll ::
    [(OptionKey, Maybe OptionValue)] ->
    Validation ParseErrors [PluginOptions -> PluginOptions]
processAll = traverse $ first (ParseErrors . pure) . uncurry processOne

toKeyValue :: GHC.CommandLineOption -> (OptionKey, Maybe OptionValue)
toKeyValue opt =
    maybe (Text.pack opt, Nothing) (bimap Text.pack (Just . Text.pack)) $
        fmap (drop 1) . flip splitAt opt <$> List.elemIndex '=' opt

{- | Parses the arguments that were given to ghc at commandline as
 "-fplugin-opt PlutusTx.Plugin:opt" or "-fplugin-opt PlutusTx.Plugin:opt=val"
-}
parsePluginOptions :: [GHC.CommandLineOption] -> Validation ParseErrors PluginOptions
parsePluginOptions = fmap (foldl' (flip ($)) defaultPluginOptions) . processAll . fmap toKeyValue
