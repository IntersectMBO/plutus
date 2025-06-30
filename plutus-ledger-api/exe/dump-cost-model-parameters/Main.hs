{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE TypeApplications    #-}

module Main (main)
where

import Parsers (Format (..), WhichLL (..), parseDumpOptions)

import PlutusCore qualified as PLC
import PlutusCore.Builtin qualified as PLC
import PlutusCore.Default.Builtins qualified as PLC
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as PLC

import PlutusLedgerApi.Common.ParamName
import PlutusLedgerApi.Common.Versions (PlutusLedgerLanguage (..))
import PlutusLedgerApi.V1.ParamName qualified as V1
import PlutusLedgerApi.V2.ParamName qualified as V2
import PlutusLedgerApi.V3.ParamName qualified as V3

import Data.Aeson qualified as A (Object, ToJSON, Value (Array, Number))
import Data.Aeson.Encode.Pretty (encodePretty)
import Data.Aeson.Key qualified as K (fromString)
import Data.Aeson.KeyMap qualified as KM (KeyMap, singleton)
import Data.ByteString.Lazy (putStr)
import Data.Int (Int64)
import Data.List.Extra (enumerate)
import Data.Map qualified as Map (lookup)
import Data.Text (Text)
import Data.Vector qualified as V (fromList)
import Options.Applicative (execParser)
import Text.Printf (printf)

-- COMMENT ABOUT WHAT THIS IS FOR.  Maybe get the help to say it too.
-- There's also the uplc option, but that sorts things.

-- Mapping of LL versions to semantic versions and parameter names for *the
-- current state of the repository*.  This MUST be updated if the mappings in
-- the PlutusLedgerApi.V<n>.EvaluationContext modules are changed.
infoFor :: PlutusLedgerLanguage -> (PLC.BuiltinSemanticsVariant PLC.DefaultFun, [Text])
infoFor =
  let paramNames :: forall a . IsParamName a => [Text]
      paramNames = fmap showParamName $ enumerate @a
  in \case
    PlutusV1 -> (PLC.DefaultFunSemanticsVariantB, paramNames @V1.ParamName)  -- <-- Is there already a function that does the second thing?
    PlutusV2 -> (PLC.DefaultFunSemanticsVariantB, paramNames @V2.ParamName)
    PlutusV3 -> (PLC.DefaultFunSemanticsVariantC, paramNames @V3.ParamName)

-- Return the current cost model parameters for a given LL version in the form
-- of a list of (name, value) pairs.
getParamsFor :: PlutusLedgerLanguage -> [(Text, Int64)]
getParamsFor ll =
  let (semvar, paramNames) = infoFor ll
      params =
        case PLC.defaultCostModelParamsForVariant semvar of
          Nothing -> error $ "Can't find default cost model parameters for " ++ show semvar
          Just p  -> p
      lookupParam name =
        case Map.lookup name params of
            Nothing -> error $ "No entry for " ++ show name ++ " in cost model for semantic variant " ++ show semvar
            Just n  -> (name, n)
  in fmap lookupParam paramNames

-- A couple of convenience functions for dealing with JSON.
mkObject :: String -> v -> KM.KeyMap v
mkObject k v = KM.singleton (K.fromString k) v

putJSON :: A.ToJSON a => a -> IO ()
putJSON = Data.ByteString.Lazy.putStr . encodePretty

-- Return the cost model parameters for a given LL in the form of a JSON object
-- containing the LL version and an array of parameter values.  This is the same
-- format that cardano-cli uses to render the protocol parameters.  Cost model
-- parameter names are not included in the protocol parameters: they used to be,
-- but not any more.
getParamsAsJSON :: PlutusLedgerLanguage -> A.Object
getParamsAsJSON ll =
  let params = getParamsFor ll
      entries = A.Array $ V.fromList $ fmap (\(_,v) -> A.Number $ fromIntegral v) params
  in mkObject (show ll) entries

printParameters :: Format -> PlutusLedgerLanguage -> IO ()
printParameters fmt ll =
  case fmt of
    Untagged -> do
      printf "\n%s:\n" $ show ll
      mapM_ (\(_,val) -> printf "  %-d\n" val) $ getParamsFor ll
    Tagged -> do
      printf "\n%s:\n" $ show ll
      mapM_ (\(name,val) -> printf "  %-12d -- %s\n" val name) $ getParamsFor ll
    JSON -> putJSON $ getParamsAsJSON ll

-- Print the cost model parameters for all ledger languages.  For JSON we have
-- to create a single object containing parameters for all ledger language
-- versions and print that; for the other formats we just print them all out in
-- sequence.
printAll :: Format -> IO ()
printAll fmt =
  case fmt of
    JSON -> putJSON $ mkObject "costModels" $ mconcat (fmap getParamsAsJSON enumerate)
    _    -> mapM_ (printParameters fmt) enumerate

main :: IO ()
main = do
  (lls, fmt) <- execParser parseDumpOptions
  case lls of
    One ll -> printParameters fmt ll
    All    -> printAll fmt

-- See
-- cardano-ledger/libs/cardano-ledger-core/src/Cardano/Ledger/Plutus/CostModels.hs
-- for how the ledger deals with cost models.  This is used in cardano-cli and
-- cardano-api as well.
