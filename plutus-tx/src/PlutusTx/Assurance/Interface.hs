{-# LANGUAGE OverloadedStrings #-}

{-| Producer for the coordinated, unpublished CIP-57/assurance dialects.
Legacy 'attachUal' and 'writeAssurance' remain available for UAL 0.5 fixtures. -}
module PlutusTx.Assurance.Interface
  ( interfaceBlueprint
  , FunctionArtifact
  , ParameterArtifact
  , compiledParameter
  , AppliedParameters
  , appliedParameters
  , writeInterfaceBundleWithBindings
  , compiledFunction
  , writeInterfaceBundleWithFunctions
  , writeInterfaceBundle
  ) where

import Codec.Extras.SerialiseViaFlat (SerialiseViaFlat (..))
import Codec.Serialise (serialise)
import Control.Lens (over)
import Control.Monad (foldM, forM, forM_, unless)
import Data.Aeson (Value (..), object, toJSON, (.=))
import Data.Aeson.Encode.Pretty (encodePretty)
import Data.Aeson.Key qualified as Key
import Data.Aeson.KeyMap qualified as KM
import Data.ByteString qualified as BS
import Data.ByteString.Base16 qualified as Base16
import Data.ByteString.Lazy qualified as LBS
import Data.List (nub)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding qualified as TE
import Data.Vector qualified as V
import PlutusCore (DefaultFun, DefaultUni)
import PlutusCore.Crypto.Hash (sha2_256)
import PlutusCore.Flat (Flat (encode))
import PlutusCore.Flat.Encoder (strictEncoder)
import PlutusCore.Flat.Filler (Filler (FillerEnd))
import PlutusTx.Assurance.Build (buildAssurance)
import PlutusTx.Assurance.Document
import PlutusTx.Assurance.Write (blueprintRef)
import PlutusTx.Blueprint.Contract (ContractBlueprint)
import PlutusTx.Blueprint.Definition.Id (definitionIdToText)
import PlutusTx.Blueprint.PlutusVersion (PlutusVersion (..))
import PlutusTx.Blueprint.Validator (ExecutionBudget (..), compiledValidator, compiledValidatorHash)
import PlutusTx.Code (CompiledCode, getPlcNoAnn)
import PlutusTx.Ual.Parser (parseArgument)
import PlutusTx.Ual.Resolve (attachUal)
import PlutusTx.Ual.Syntax
  ( ArgumentEncoding (..)
  , ModuleUal (..)
  , OnchainDecl (..)
  , OnchainKind (..)
  , ResolvedArgument (..)
  , UalArgument (..)
  )
import UntypedPlutusCore qualified as UPLC
import Prelude

{-| A compiled function, constructed from actual Plinth output. Its interface
is derived from ONCHAIN, not supplied a second time by the caller. -}
data FunctionArtifact = FunctionArtifact Text BS.ByteString

compiledFunction :: Text -> CompiledCode a -> FunctionArtifact
compiledFunction ident code = FunctionArtifact ident bytes
  where
    program = over UPLC.progTerm (UPLC.termMapNames UPLC.unNameDeBruijn) (getPlcNoAnn code)
    bytes = LBS.toStrict (serialise (SerialiseViaFlat (UPLC.UnrestrictedProgram program)))

{-| A compiled parameter value. The checker independently requires a closed
value in the declared wire encoding; compiling an arbitrary expression does
not establish that obligation. -}
newtype ParameterArtifact = ParameterArtifact (UPLC.Program UPLC.DeBruijn DefaultUni DefaultFun ())

compiledParameter :: CompiledCode a -> ParameterArtifact
compiledParameter = ParameterArtifact . over UPLC.progTerm (UPLC.termMapNames UPLC.unNameDeBruijn) . getPlcNoAnn

data AppliedParameters = AppliedParameters [BS.ByteString] BS.ByteString

{-| Apply without optimization so the consumer can verify the exact ordered
template application independently of the compiler. -}
appliedParameters :: CompiledCode a -> [ParameterArtifact] -> Either String AppliedParameters
appliedParameters template parameters = do
  let ParameterArtifact program = compiledParameter template
      programs = [p | ParameterArtifact p <- parameters]
  applied <- foldM (\f x -> either (Left . show) Right (UPLC.applyProgram f x)) program programs
  pure
    ( AppliedParameters
        [ strictEncoder (UPLC.sizeTerm t 0 + 8) (UPLC.encodeTerm t <> encode FillerEnd)
        | UPLC.Program _ _ t <- programs
        ]
        (LBS.toStrict (serialise (SerialiseViaFlat (UPLC.UnrestrictedProgram applied))))
    )

hex :: BS.ByteString -> Text
hex = TE.decodeUtf8 . Base16.encode

-- Keep references finite: function schemas resolve against assurance.definitions.
-- Cycles are validated by the checking profile, without truncating their depth.
functionSchema :: Value -> UalArgument -> ResolvedArgument -> Either String Value
functionSchema defs a r = case argEncoding a of
  AsScott -> Left "Scott function encoding is unsupported"
  AsData -> do
    let key = definitionIdToText (resolvedDefinitionId r)
    _ <- field key defs
    pure (object ["$ref" .= ("#/definitions/" <> T.replace "/" "~1" (T.replace "~" "~0" key))])
  AsNative -> do
    kind <-
      maybe (Left "unsupported native function type") Right $
        lookup
          (argTypeName a)
          [ ("Integer", "#integer")
          , ("BuiltinByteString", "#bytes")
          , ("BuiltinString", "#string")
          , ("Bool", "#boolean")
          , ("BuiltinUnit", "#unit")
          ]
    pure (object ["dataType" .= (kind :: Text)])

functionRegistry
  :: [ModuleUal] -> ContractBlueprint -> [FunctionArtifact] -> Either String [(Text, Value)]
functionRegistry modules bp artifacts = do
  let decls = [d | m <- modules, d <- ualOnchain m]
      ids = map onchainName decls
      fs = filter ((== Function) . onchainKind) decls
      artifactIds = [i | FunctionArtifact i _ <- artifacts]
  unless (length (nub ids) == length ids) (Left "duplicate ONCHAIN target id")
  unless (length (nub artifactIds) == length artifactIds) (Left "duplicate compiled function id")
  unless
    (length artifactIds == length fs && all (`elem` artifactIds) (map onchainName fs))
    (Left "every function ONCHAIN needs exactly one compiled function artifact")
  let defs = maybe (object []) id (optional "definitions" (toJSON bp))
  forM fs $ \d -> do
    let ident = onchainName d
    bytes <- case [b | FunctionArtifact i b <- artifacts, i == ident] of
      [b] | not (BS.null b) -> Right b
      _ -> Left "missing compiled function bytes"
    unless
      (length (onchainArgs d) == length (onchainResolvedArgs d))
      (Left "unresolved function arguments")
    args <- sequence (zipWith (functionSchema defs) (onchainArgs d) (onchainResolvedArgs d))
    resultArg <- either (Left . show) Right (parseArgument (onchainLine d) (onchainResult d))
    resultResolved <- maybe (Left "unresolved function result") Right (onchainResolvedResult d)
    result <- functionSchema defs resultArg resultResolved
    version <- maybe (Left "function requires explicit Plutus version") Right (onchainVersion d)
    pure
      ( ident
      , object
          [ "compiledCode" .= hex bytes
          , "serialization" .= ("cbor-flat" :: Text)
          , "hash" .= object ["alg" .= ("sha256" :: Text), "digest" .= hex (sha2_256 bytes)]
          , "plutusVersion" .= version
          , "arguments" .= args
          , "result" .= result
          ]
      )

base :: Text
base = "https://cips.cardano.org/cips/cip57/extensions/compiled-interface/v1/"

field :: Text -> Value -> Either String Value
field k (Object o) = maybe (Left ("missing " <> T.unpack k)) Right (KM.lookup (Key.fromText k) o)
field k _ = Left ("expected object for " <> T.unpack k)

array :: Value -> Either String [Value]
array (Array a) = Right (V.toList a)
array _ = Left "expected array"

text :: Value -> Either String Text
text (String s) = Right s
text _ = Left "expected string"

set :: Text -> Value -> Value -> Value
set k v (Object o) = Object (KM.insert (Key.fromText k) v o)
set _ _ v = v

remove :: Text -> Value -> Value
remove k (Object o) = Object (KM.delete (Key.fromText k) o)
remove _ v = v

optional :: Text -> Value -> Maybe Value
optional k (Object o) = KM.lookup (Key.fromText k) o
optional _ _ = Nothing

resolve :: Value -> [Text] -> Value -> Either String Value
resolve defs seen s = case optional "$ref" s of
  Nothing -> Right s
  Just r -> do
    ref <- text r
    unless ("#/definitions/" `T.isPrefixOf` ref) (Left "only local definitions are supported")
    let key = T.replace "~0" "~" (T.replace "~1" "/" (T.drop 14 ref))
    unless (key `notElem` seen) (Left "unguarded alias cycle in interface schema")
    field key defs >>= resolve defs (key : seen)

{-| Emit interface references, preserving the parameter schema as the single
encoding authority. Runtime ONCHAIN binders must be raw BuiltinData, even if
a blueprint describes a narrower datum/redeemer domain. -}
interfaceBlueprint :: [ModuleUal] -> ContractBlueprint -> Either String Value
interfaceBlueprint modules bp = do
  attached <- either (Left . show) Right (attachUal modules bp)
  let original = toJSON attached
  pre <- field "preamble" original
  -- The legacy preamble encoder represents absent optional fields as null.
  -- The compiled-interface dialect requires those fields to be omitted.
  let cleanPre =
        foldr
          (\k value -> if optional k value == Just Null then remove k value else value)
          pre
          ["description", "license"]
      doc = set "preamble" cleanPre original
  version <- field "preamble" doc >>= field "plutusVersion" >>= text
  unless (version `elem` ["v1", "v2", "v3"]) (Left "unsupported ledger calling convention")
  let defs = maybe (object []) id (optional "definitions" doc)
  vs <- field "validators" doc >>= array
  converted <- traverse (convert defs version) vs
  vocab <- field "$vocabulary" doc
  pure $
    set "$schema" (String (base <> "schema.json")) $
      set "$vocabulary" (set (base <> "vocabulary") (Bool True) vocab) $
        set "validators" (toJSON converted) doc
  where
    convert defs version v = do
      _ <- field "id" v >>= text
      redeemer <- field "redeemer" v
      purposes <- case optional "purpose" redeemer of
        Just (String p) -> Right [p]
        Just p -> field "oneOf" p >>= array >>= traverse text
        Nothing -> Left "extended interface requires explicit redeemer purposes"
      unless
        (not (null purposes) && length (nub purposes) == length purposes)
        (Left "interface purposes must be nonempty and unique")
      params <- maybe (Right []) array (optional "parameters" v)
      args <- field "arguments" v >>= array
      let n = length params
      invocations <- forM purposes $ \purpose -> do
        unless
          (purpose `elem` ["spend", "mint", "withdraw", "publish", "vote", "propose"])
          (Left "unknown ledger purpose")
        unless
          (version == "v3" || purpose `notElem` ["vote", "propose"])
          (Left "vote/propose require ledger-v3")
        let roles =
              if version == "v3"
                then ["context"]
                else
                  if purpose == "spend"
                    then ["datum", "redeemer", "context"]
                    else ["redeemer", "context"]
        unless
          (length args == n + length roles)
          (Left "ONCHAIN arity does not match complete ledger invocation")
        forM_ (zip params (take n args)) $ \(param, arg) -> do
          ps <- field "schema" param >>= resolve defs []
          as <- field "schema" arg >>= resolve defs []
          enc <- field "encoding" arg >>= text
          -- Haskell Integer/ByteString normally derive a Data schema; an
          -- explicit native boundary retains the same host primitive type.
          let samePrimitive =
                (optional "dataType" ps, optional "dataType" as)
                  `elem` [ (Just (String "#integer"), Just (String "integer"))
                         , (Just (String "#bytes"), Just (String "bytes"))
                         ]
          unless
            (ps == as || (enc == "asNative" && samePrimitive))
            (Left "ONCHAIN parameter schema differs from blueprint parameter")
          let native =
                maybe False (\x -> case x of String t -> "#" `T.isPrefixOf` t; _ -> False) (optional "dataType" ps)
          unless
            (enc == if native then "asNative" else "asData")
            (Left "ONCHAIN parameter encoding contradicts schema (Scott is unsupported)")
          pure ()
        forM_ (drop n args) $ \arg -> do
          s <- field "schema" arg >>= resolve defs []
          enc <- field "encoding" arg >>= text
          unless
            ( enc == "asData"
                && all (\k -> optional k s == Nothing) ["dataType", "anyOf", "oneOf", "allOf", "not"]
            )
            (Left "runtime ONCHAIN arguments must be raw BuiltinData")
          pure ()
        forM_ roles $ \role -> case role of
          "context" -> pure ()
          _ -> do
            slot <- field role v
            case optional "purpose" slot of
              Nothing -> pure ()
              Just (String p) -> unless (p == purpose) (Left "runtime purpose mismatch")
              Just p -> do
                ps <- field "oneOf" p >>= array >>= traverse text
                unless (purpose `elem` ps) (Left "runtime purpose mismatch")
        let paramRefs =
              [ object ["role" .= ("parameter" :: Text), "source" .= ("/parameters/" <> T.pack (show i))]
              | i <- [0 .. n - 1]
              ]
            runtime role = object (["role" .= role] <> ["source" .= ("/" <> role) | role /= "context"])
        pure $ object ["purpose" .= purpose, "arguments" .= (paramRefs <> map runtime roles)]
      pure
        $ set
          "interface"
          (object ["callingConvention" .= ("ledger-" <> version), "invocations" .= invocations])
        $ remove "arguments"
        $ remove "budget" v

{-| Write plutus.json, assurance.json and one digest-bound context per claim in
the working directory. The supplied environment manifest must describe the
actual checking environment; the checker validates it before execution.
The default API uses universal parameters and explicit semantic step budgets.
Use writeInterfaceBundleWithBindings for a fully specialized deployment. -}
writeInterfaceBundle
  :: FilePath -> AssurancePreamble -> Text -> [ModuleUal] -> ContractBlueprint -> IO ()
writeInterfaceBundle environment preamble defaultId modules bp =
  writeInterfaceBundleWithFunctions environment preamble defaultId modules bp []

writeInterfaceBundleWithFunctions
  :: FilePath
  -> AssurancePreamble
  -> Text
  -> [ModuleUal]
  -> ContractBlueprint
  -> [FunctionArtifact]
  -> IO ()
writeInterfaceBundleWithFunctions environment preamble defaultId modules bp artifacts =
  writeInterfaceBundleWithBindings environment preamble defaultId modules bp artifacts []

{-| Each binding names a property and validator, then supplies every parameter
in declaration order. Properties refer to the remaining runtime arguments. -}
writeInterfaceBundleWithBindings
  :: FilePath
  -> AssurancePreamble
  -> Text
  -> [ModuleUal]
  -> ContractBlueprint
  -> [FunctionArtifact]
  -> [(Text, Text, AppliedParameters)]
  -> IO ()
writeInterfaceBundleWithBindings environment preamble defaultId modules bp artifacts bindings = do
  let die = either fail pure
      write f = LBS.writeFile f . (<> "\n") . encodePretty
  functions <- die (functionRegistry modules bp artifacts)
  let definitions = maybe (object []) id (optional "definitions" (toJSON bp))
  extended <- die (interfaceBlueprint modules bp)
  attached <- die (either (Left . show) Right (attachUal modules bp))
  validators <- die (field "validators" (toJSON attached) >>= array)
  extendedValidators <- die (field "validators" extended >>= array)
  envRef <- blueprintRef (T.pack environment) environment
  write "plutus.json" extended
  ref <- blueprintRef "plutus.json" "plutus.json"
  assurance <- die (either (Left . show) Right (buildAssurance preamble ref defaultId modules))
  let bindingIds = [(pid, vid) | (pid, vid, _) <- bindings]
  unless (length bindingIds == length (nub bindingIds)) (fail "duplicate applied binding")
  forM_ bindingIds $ \(pid, vid) ->
    unless
      ( any
          (\p -> propertyIdent p == pid && vid `elem` propertyValidators p)
          (assuranceProperties assurance)
          && vid `notElem` map fst functions
      )
      (fail "applied binding does not name a scoped validator")
  contexts <- forM (assuranceProperties assurance) $ \prop -> do
    targets <- forM (propertyValidators prop) $ \vid -> do
      case lookup vid functions of
        Just f -> do
          d <- die $ case [d | m <- modules, d <- ualOnchain m, onchainName d == vid] of
            [d] -> Right d
            _ -> Left "ambiguous function target"
          (steps, sem) <- case onchainBudget d of
            Just (MkSemanticStepBudget n sem) -> pure (toJSON n, toJSON sem)
            _ -> fail "function requires explicit steps and semantics"
          h <- die (field "hash" f)
          let iface = set "definitions" definitions (remove "compiledCode" (remove "hash" f))
          pure (object ["function" .= vid, "functionHash" .= h, "functionInterface" .= iface], steps, sem)
        Nothing -> do
          v <- die $ case filter (\v -> optional "id" v == Just (String vid)) validators of
            [v] -> Right v
            _ -> Left "checking target is missing or ambiguous"
          ev <- die $ case filter (\candidate -> optional "id" candidate == Just (String vid)) extendedValidators of
            [ev] -> Right ev
            _ -> Left "extended target is missing or ambiguous"
          invs <- die (field "interface" ev >>= field "invocations" >>= array)
          inv <- die $ case invs of [i] -> Right i; _ -> Left "UAL profile requires one invocation purpose per target"
          purpose <- die (field "purpose" inv)
          budget <- die (field "budget" v)
          steps <- die (field "steps" budget)
          semantics <- die (field "semantics" budget)
          unless
            (optional "exCPU" budget == Nothing && optional "exMem" budget == Nothing)
            (fail "step checking cannot use ledger units")
          params <- case [a | (pid, target, a) <- bindings, pid == propertyIdent prop, target == vid] of
            [] -> pure (object ["mode" .= ("universal" :: Text)])
            [AppliedParameters values code] -> do
              slots <- die (maybe (Right []) array (optional "parameters" ev))
              unless
                (not (null values) && length values == length slots)
                (fail "applied parameters must cover every parameter")
              let prefix = "applied-" <> T.unpack (propertyIdent prop) <> "-" <> T.unpack vid
              terms <- forM (zip [0 :: Int ..] values) $ \(i, bytes) -> do
                let name = prefix <> "-" <> show i <> ".flat"
                BS.writeFile name bytes
                termRef <- blueprintRef (T.pack name) name
                pure (object ["parameter" .= ("/parameters/" <> T.pack (show i)), "term" .= termRef])
              let name = prefix <> ".cbor"
              BS.writeFile name code
              codeRef <- blueprintRef (T.pack name) name
              version <- die (field "preamble" extended >>= field "plutusVersion" >>= text)
              language <- die $ case version of
                "v1" -> Right PlutusV1
                "v2" -> Right PlutusV2
                "v3" -> Right PlutusV3
                _ -> Left "unknown language"
              pure
                ( object
                    [ "mode" .= ("applied" :: Text)
                    , "values" .= terms
                    , "appliedScript" .= codeRef
                    , "appliedScriptHash" .= hex (compiledValidatorHash (compiledValidator language code))
                    ]
                )
            _ -> fail "duplicate applied binding"
          pure
            ( object
                ["validator" .= vid, "purpose" .= purpose, "parameters" .= params]
            , steps
            , semantics
            )
    (steps, sem) <- die $ case nub [(s, e) | (_, s, e) <- targets] of
      [setting] -> Right setting
      _ -> Left "all targets of a property must use the same execution settings"
    let name = "checking-" <> T.unpack (propertyIdent prop) <> ".json"
    write name $
      object
        [ "$schema" .= ("https://cips.cardano.org/cips/cipXXXX/schemas/checking-context.json" :: Text)
        , "profile" .= ("https://cips.cardano.org/cips/cipXXXX/profiles/uplc-step-check/v1" :: Text)
        , "environment" .= envRef
        , "execution"
            .= object
              [ "semanticsVariant" .= sem
              , "acceptance" .= ("evaluation" :: Text)
              , "budget" .= object ["kind" .= ("cek-steps" :: Text), "steps" .= steps]
              ]
        , "targets" .= [t | (t, _, _) <- targets]
        ]
    contextRef <- blueprintRef (T.pack name) name
    pure (propertyIdent prop, toJSON contextRef)
  let doc = toJSON assurance
      props =
        [ set "checkingContext" (String (propertyIdent p)) $
            set
              "scope"
              ( object
                  (["validators" .= vs | not (null vs)] <> ["functions" .= fs | not (null fs)])
              )
              (toJSON p)
        | p <- assuranceProperties assurance
        , let fs = filter (`elem` map fst functions) (propertyValidators p)
        , let vs = filter (`notElem` map fst functions) (propertyValidators p)
        ]
      langs =
        object
          [ "ual"
              .= object
                [ "name" .= ("Universal Annotation Language" :: Text)
                , "version" .= ("0.6-draft" :: Text)
                , "uri" .= ("https://github.com/input-output-hk/UniversalAnnotationLanguage" :: Text)
                ]
          ]
  write "assurance.json" $
    set "$schema" (String "https://cips.cardano.org/cips/cipXXXX/schemas/assurance-v2.json") $
      set "definitions" definitions $
        set "functions" (Object (KM.fromList [(Key.fromText k, v) | (k, v) <- functions])) $
          set "languages" langs $
            set "checkingContexts" (Object (KM.fromList [(Key.fromText k, v) | (k, v) <- contexts])) $
              set "properties" (toJSON props) doc
