{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

-- TODO: Extend this to handle the different variants of the cost model

module PlutusCore.Evaluation.Machine.SimpleBuiltinCostModel
  ( BuiltinCostMap
  , BuiltinCostKeyMap
  , toSimpleBuiltinCostModel
  , defaultSimpleBuiltinCostModel
  ) where

import Data.Aeson (Result (..), eitherDecodeFileStrict, fromJSON, toJSON)
import Data.Aeson.Key as Key (toText)
import Data.Aeson.KeyMap qualified as KeyMap
import Data.Aeson.THReader (readJSONFromFile)
import Data.Bifunctor
import Data.Text (Text, replace)
import PlutusCore.DataFilePaths qualified as DFP
import PlutusCore.Evaluation.Machine.BuiltinCostModel
import PlutusCore.Evaluation.Machine.CostModel.BuiltinCostModelC (builtinCostModelC)
import PlutusCore.Evaluation.Machine.CostingFun.SimpleJSON
import System.IO.Unsafe

type BuiltinCostMap = [(Text, CpuAndMemoryModel)]
type BuiltinCostKeyMap = KeyMap.KeyMap CpuAndMemoryModel

{-| The default builtin cost map.
TODO: maybe we should take account of the semantic variant here. -}
defaultBuiltinCostKeyMap :: BuiltinCostKeyMap
defaultBuiltinCostKeyMap = builtinCostModelToBuiltinCostKeyMap builtinCostModelC

-- replace underscores _ by dashes -
builtinName :: Text -> Text
builtinName = replace "_" "-"

toSimpleBuiltinCostModel :: BuiltinCostKeyMap -> BuiltinCostMap
toSimpleBuiltinCostModel m = map (first (builtinName . toText)) (KeyMap.toList m)

defaultSimpleBuiltinCostModel :: BuiltinCostMap
defaultSimpleBuiltinCostModel = toSimpleBuiltinCostModel defaultBuiltinCostKeyMap

-- We rely on
builtinCostModelToBuiltinCostKeyMap :: BuiltinCostModel -> BuiltinCostKeyMap
builtinCostModelToBuiltinCostKeyMap model = do
  unsafePerformIO $ do
    r <- eitherDecodeFileStrict "plutus-core/cost-model/data/builtinCostModelC.json"
    case r of
      Left str -> error ("Uexpected malformed json for builtin model: " <> str)
      Right x -> return x

-- case fromJSON (toJSON model) of
-- Error str -> error ("Uexpected malformed json for builtin model: " <> str)
-- Success x -> x
