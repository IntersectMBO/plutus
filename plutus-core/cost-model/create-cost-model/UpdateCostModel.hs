module Main where

import PlutusCore.DataFilePaths

import Data.Aeson.Encode.Pretty
import Data.ByteString.Lazy qualified as BSL

import CostModelCreation

{- See Note [Creation of the Cost Model]
-}
main :: IO ()
main = do
  model <- createBuiltinCostModel
  BSL.writeFile builtinCostModelFile $ encodePretty' (defConfig { confCompare = \_ _-> EQ }) model
