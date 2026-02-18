{-# LANGUAGE OverloadedStrings #-}

-- TODO: Extend this to handle the different variants of the cost model

{-| A program to parse a representation of costing functions for Plutus Core
   builtins and produce a simple cost model which can be used from Agda and other
   executables -}
module PlutusCore.Evaluation.Machine.SimpleBuiltinCostModel
  ( BuiltinCostMap
  , BuiltinCostKeyMap
  , toSimpleBuiltinCostModel
  , defaultSimpleBuiltinCostModel
  ) where

import Data.Aeson (ToJSON, encode)
import Data.Aeson.Key as Key (toText)
import Data.Aeson.KeyMap qualified as KeyMap
import Data.Aeson.Types (parseEither, parseMaybe)
import Data.Bifunctor
import Data.ByteString.Lazy qualified as BSL
import Data.Text (Text, replace)
import PlutusCore.Evaluation.Machine.BuiltinCostModel
import PlutusCore.Evaluation.Machine.CostModel.Generated.BuiltinCostModelC (builtinCostModelC)
import PlutusCore.Evaluation.Machine.CostingFun.SimpleJSON

type BuiltinCostMap = [(Text, CpuAndMemoryModel)]
type BuiltinCostKeyMap = KeyMap.KeyMap CpuAndMemoryModel

{-| The default builtin cost map.
TODO: maybe we should take account of the semantic variant here. -}
defaultBuiltinCostKeyMap :: BuiltinCostKeyMap
defaultBuiltinCostKeyMap = undefined

-- replace underscores _ by dashes -
builtinName :: Text -> Text
builtinName = replace "_" "-"

toSimpleBuiltinCostModel :: BuiltinCostKeyMap -> BuiltinCostMap
toSimpleBuiltinCostModel m = map (first (builtinName . toText)) (KeyMap.toList m)

defaultSimpleBuiltinCostModel :: BuiltinCostMap
defaultSimpleBuiltinCostModel = toSimpleBuiltinCostModel defaultBuiltinCostKeyMap
