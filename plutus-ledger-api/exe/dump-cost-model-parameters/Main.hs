{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}

module Main (main)
where

import Parsers (Format (..), WhichLL (..), parseDumpOptions)

import PlutusCore qualified as PLC
import PlutusCore.Builtin qualified as PLC
import PlutusCore.Default.Builtins qualified as PLC
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as PLC

import PlutusLedgerApi.Common (IsParamName, PlutusLedgerLanguage (..), showParamName)
import PlutusLedgerApi.V1 qualified as V1
import PlutusLedgerApi.V2 qualified as V2
import PlutusLedgerApi.V3 qualified as V3

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

{-| This executable prints out the cost model parameters according to the various
    `PlutusLedgerApi.V<n>.ParamName types`.  These determine both the cost model
    parameters included in the protocol parameters (and hence which Plutus
    builtins are available to each Plutus ledger language version) and the order
    in which they occur.  The protocol parameters and the ledger both treat the
    cost model parameters as ordered lists of integers and know nothing about
    the names of the parameters (see
    `cardano-ledger/libs/cardano-ledger-core/src/Cardano/Ledger/Plutus/CostModels.hs`
    for how the ledger (and also cardano-api and cardano-cli) deals with cost
    models), and the `ParamName` types provide the link between the lists of
    parameters and the complex structure used to represent a cost model in
    Plutus Core.  New cost models (possibly enabling new builtins) are
    propagated to the chain by protocol updates which update the cost model
    parameters, and this executable produces lists of cost model parameters in a
    form suitable for inclusion in the protocol parameters, and so can be helpful
    when we need to propose new parameters for use on the chain, and to check
    that the on-chain parameters are as expected.  Note that this code deals
    only with the cost model parameters in the current state of the `plutus`
    repository, which may differ from those on the chain: specifically, the cost
    model parameters dealt with by this code will often be those which are
    expected to come into effect at the next hard fork and hence will be ahead
    of those currently in use for new script executions on the chain.  The exact
    structure of the cost model used by a particular ledger language is
    determined by a _semantic variant_ which depends on both the ledger language
    and the protocol version (see the `mkEvaluationContext` functions in the
    various `EvaluationContext` files), and this code will need to be updated
    if, for example, a new Plutus Ledger language is added or the structure of
    the cost model used by an existing ledger language changes. -}

-- Mapping of LL versions to semantic versions and parameter names for *the
-- current state of the repository*.  This MUST be updated if the mappings in
-- the PlutusLedgerApi.V<n>.EvaluationContext modules are changed.
infoFor :: PlutusLedgerLanguage -> (PLC.BuiltinSemanticsVariant PLC.DefaultFun, [Text])
infoFor =
  let paramNames :: forall a. IsParamName a => [Text]
      paramNames = fmap showParamName $ enumerate @a
   in \case
        PlutusV1 -> (PLC.DefaultFunSemanticsVariantD, paramNames @V1.ParamName)
        PlutusV2 -> (PLC.DefaultFunSemanticsVariantD, paramNames @V2.ParamName)
        PlutusV3 -> (PLC.DefaultFunSemanticsVariantE, paramNames @V3.ParamName)

-- Return the current cost model parameters for a given LL version in the form
-- of a list of (name, value) pairs ordered by name according to the relevant
-- `ParamName` type.
getParamsFor :: PlutusLedgerLanguage -> [(Text, Int64)]
getParamsFor ll =
  let (semvar, paramNames) = infoFor ll
      params =
        case PLC.defaultCostModelParamsForVariant semvar of
          Nothing ->
            error $
              "Can't find default cost model parameters for "
                ++ show semvar
          Just p -> p
      lookupParam name =
        case Map.lookup name params of
          Nothing ->
            error $
              "No entry for "
                ++ show name
                ++ " in cost model for semantic variant "
                ++ show semvar
          Just n -> (name, n)
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
      entries = A.Array $ V.fromList $ fmap (\(_, v) -> A.Number $ fromIntegral v) params
   in mkObject (show ll) entries

printParameters :: Format -> PlutusLedgerLanguage -> IO ()
printParameters fmt ll =
  case fmt of
    Untagged -> do
      printf "%s:\n" $ show ll
      mapM_ (\(_, val) -> printf "  %-d\n" val) $ getParamsFor ll
      printf "\n"
    Tagged -> do
      printf "%s:\n" $ show ll
      mapM_ (\(name, val) -> printf "  %-12d -- %s\n" val name) $ getParamsFor ll
      printf "\n"
    JSON -> putJSON $ getParamsAsJSON ll

-- Print the cost model parameters for all ledger languages.  For JSON we have
-- to create a single object containing parameters for all ledger language
-- versions and print that; for the other formats we just print them all out in
-- sequence.
printAll :: Format -> IO ()
printAll fmt =
  case fmt of
    JSON -> putJSON $ mkObject "costModels" $ mconcat (fmap getParamsAsJSON enumerate)
    _ -> mapM_ (printParameters fmt) enumerate

main :: IO ()
main = do
  (lls, fmt) <- execParser parseDumpOptions
  case lls of
    One ll -> printParameters fmt ll
    All -> printAll fmt
