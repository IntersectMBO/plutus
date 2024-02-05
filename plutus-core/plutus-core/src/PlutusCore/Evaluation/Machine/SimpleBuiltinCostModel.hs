{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

{- | A program to parse a JSON representation of costing functions for Plutus Core
   builtins and and produce a simple cost model which can be used from Agda and other
   executables
-}
module PlutusCore.Evaluation.Machine.SimpleBuiltinCostModel (
  BuiltinCostMap,
  defaultSimpleBuiltinCostModel,
) where

import Data.Aeson.Key as Key (toText)
import Data.Aeson.KeyMap qualified as KeyMap
import Data.Aeson.THReader (readJSONFromFile)
import Data.Bifunctor
import Data.Text (Text, replace)
import PlutusCore.DataFilePaths qualified as DFP
import PlutusCore.Evaluation.Machine.CostingFun.SimpleJSON

type BuiltinCostMap = [(Text, CpuAndMemoryModel)]

-- | The default builtin cost map.
builtinCostKeyMap :: KeyMap.KeyMap CpuAndMemoryModel
builtinCostKeyMap =
  $$(readJSONFromFile DFP.builtinCostModelFile)

-- replace underscores _ by dashes -
builtinName :: Text -> Text
builtinName = replace "_" "-"

defaultSimpleBuiltinCostModel :: BuiltinCostMap
defaultSimpleBuiltinCostModel = map (first (builtinName . toText)) (KeyMap.toList builtinCostKeyMap)
