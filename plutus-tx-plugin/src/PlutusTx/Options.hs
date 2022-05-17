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
 TODO: only define the possitive version and automaticalaly get tne "no-" version.
-}
pluginOptions :: Map OptionKey PluginOption
pluginOptions =
    Map.fromList
        [ let k = "no-typecheck"
           in (k, PluginOption typeRep (setFalse k) posDoTypecheck mempty)
        , let k = "defer-errors"
           in (k, PluginOption typeRep (setTrue k) posDeferErrors mempty)
        , let k = "no-context"
           in (k, PluginOption typeRep (flag (const 0) k) posContextLevel mempty)
        , let k = "debug-context"
           in (k, PluginOption typeRep (flag (const 3) k) posContextLevel mempty)
        , let k = "dump-pir"
           in (k, PluginOption typeRep (setTrue k) posDumpPir mempty)
        , let k = "dump-plc"
           in (k, PluginOption typeRep (setTrue k) posDumpPlc mempty)
        , let k = "dump-uplc"
           in (k, PluginOption typeRep (setTrue k) posDumpUPlc mempty)
        , let k = "no-optimize"
           in (k, PluginOption typeRep (setFalse k) posOptimize mempty)
        , let k = "pedantic"
           in (k, PluginOption typeRep (setTrue k) posPedantic mempty)
        , let k = "verbose"
           in (k, PluginOption typeRep (setTrue k) posVerbose mempty)
        , let k = "debug"
           in (k, PluginOption typeRep (setTrue k) posDebug mempty)
        , let k = "max-simplifier-iterations"
           in (k, PluginOption typeRep (intOption k) posMaxSimplifierIterations mempty)
        , let k = "no-simplifier-unwrap-cancel"
           in (k, PluginOption typeRep (setFalse k) posDoSimplifierUnwrapCancel mempty)
        , let k = "no-simplifier-beta"
           in (k, PluginOption typeRep (setFalse k) posDoSimplifierBeta mempty)
        , let k = "no-simplifier-inline"
           in (k, PluginOption typeRep (setFalse k) posDoSimplifierInline mempty)
        , let k = "no-simplifier-remove-dead-bindings"
           in (k, PluginOption typeRep (setFalse k) posDoSimplifierRemoveDeadBindings mempty)
        , let k = "profile-all"
           in (k, PluginOption typeRep (flag (const All) k) posProfile mempty)
        , let k = "coverage-all"
           in (k, PluginOption typeRep (setTrue k) posCoverageAll mempty)
        , let k = "coverage-location"
           in (k, PluginOption typeRep (setTrue k) posCoverageLocation mempty)
        , let k = "coverage-boolean"
           in (k, PluginOption typeRep (setTrue k) posCoverageBoolean mempty)
        , let k = "remove-trace"
           in (k, PluginOption typeRep (setTrue k) posRemoveTrace mempty)
        ]

flag :: (a -> a) -> OptionKey -> Maybe OptionValue -> Validation ParseError (a -> a)
flag f k = maybe (Success f) (Failure . UnexpectedValue k)

setTrue :: OptionKey -> Maybe OptionValue -> Validation ParseError (Bool -> Bool)
setTrue = flag (const True)

setFalse :: OptionKey -> Maybe OptionValue -> Validation ParseError (Bool -> Bool)
setFalse = flag (const False)

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
processOne key val = case Map.lookup key pluginOptions of
    Just (PluginOption _ f field _) -> over field <$> f val
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
