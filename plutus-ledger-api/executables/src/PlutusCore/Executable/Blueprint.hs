{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module PlutusCore.Executable.Blueprint
  ( BlueprintValidator (..)
  , readBlueprint
  , writeBlueprint
  ) where

import PlutusCore.Executable.AstIO (decodeUplcHex, encodeUplcHex)
import PlutusCore.Executable.Types
import PlutusLedgerApi.Common

import Data.Aeson (Value (..))
import Data.Aeson qualified as Aeson
import Data.Aeson.Encode.Pretty (encodePretty)
import Data.Aeson.Key qualified as Key
import Data.Aeson.KeyMap qualified as KM
import Data.ByteString.Lazy qualified as BSL
import Data.Either
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding qualified as T
import Data.Vector qualified as V

-- | A validator in a blueprint.
data BlueprintValidator = BlueprintValidator
  { bvTitle :: Text
  , bvCode :: UplcProg ()
  }

-- | Reads a blueprint file, extracts the validators, and returns (validators, entire json).
readBlueprint :: Input -> IO ([BlueprintValidator], Value)
readBlueprint inp = do
  bytes <- case inp of
    FileInput file -> BSL.readFile file
    StdInput -> BSL.getContents
  case Aeson.eitherDecode bytes of
    Left err -> error $ "Failed to parse blueprint: " ++ err
    Right val -> pure (extractValidators val, val)

extractValidators :: Value -> [BlueprintValidator]
extractValidators (Object obj) =
  case KM.lookup "validators" obj of
    Just (Array arr) -> map parseValidator (V.toList arr)
    Just _ -> error "Blueprint: 'validators' field is not an array"
    Nothing -> []
extractValidators _ = error "Blueprint: top-level value is not an object"

parseValidator :: Value -> BlueprintValidator
parseValidator (Object obj) =
  BlueprintValidator
    { bvTitle = case KM.lookup (Key.fromText "title") obj of
        Just (String t) -> t
        _ -> "<untitled>"
    , bvCode = case KM.lookup (Key.fromText "compiledCode") obj of
        Just (String hex) -> decodeUplcHex hex
        _ -> error "Blueprint: validator missing `compiledCode'"
    }
parseValidator _ = error "Blueprint: validator entry is not an object"

readPlutusVersion :: Text -> PlutusLedgerLanguage
readPlutusVersion = \case
  "v1" -> PlutusV1
  "v2" -> PlutusV2
  "v3" -> PlutusV3
  other -> error $ "Unknown plutusVersion in blueprint: " <> T.unpack other

getPlutusVersion :: Value -> PlutusLedgerLanguage
getPlutusVersion (Object obj) =
  case KM.lookup (Key.fromText "preamble") obj of
    Just (Object preamble) ->
      case KM.lookup (Key.fromText "plutusVersion") preamble of
        Just (String v) -> readPlutusVersion v
        _ -> error "Blueprint: preamble missing 'plutusVersion'"
    _ -> error "Blueprint: missing 'preamble' object"
getPlutusVersion _ = error "Blueprint: top-level value is not an object"

writeBlueprint :: Output -> Value -> [UplcProg ann] -> IO ()
writeBlueprint outp original optimisedProgs =
  let updated = updateValidators original optimisedProgs
   in case outp of
        FileOutput file -> BSL.writeFile file (encodePretty updated)
        StdOutput -> BSL.putStr (encodePretty updated)
        NoOutput -> pure ()

updateValidators :: Value -> [UplcProg ann] -> Value
updateValidators top@(Object obj) optimisedProgs =
  let key = Key.fromText "validators"
      ver = getPlutusVersion top
   in case KM.lookup key obj of
        Just arr -> Object $ KM.insert key (updateArr ver arr) obj
        Nothing -> Object obj -- no validator in blueprint
  where
    updateArr ver (Array arr)
      | V.length arr == length optimisedProgs =
          Array $ V.zipWith (updateOne ver) arr (V.fromList optimisedProgs)
      | otherwise =
          error $
            "Blueprint: mismatch between number of validators ("
              ++ show (V.length arr)
              ++ ") and optimised programs ("
              ++ show (length optimisedProgs)
              ++ ")"
    updateArr _ other = other
    updateOne ver (Object oldValidatorObj) optimisedProg =
      let hex = encodeUplcHex optimisedProg
          hash =
            fromRight (error $ "Invalid validator in blueprint: " <> T.unpack hex) $
              hashScriptHex ver (T.encodeUtf8 hex)
       in Object
            . KM.insert (Key.fromText "compiledCode") (String hex)
            . KM.insert (Key.fromText "hash") (String $ T.decodeUtf8 hash)
            $ oldValidatorObj
    updateOne _ other _ = other
updateValidators other _ = other
