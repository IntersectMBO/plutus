module Main where

import           PlutusCore.FilePaths

import           Data.Aeson.Encode.Pretty
import qualified Data.ByteString.Lazy     as BSL

import           CostModelCreation

{- See Note [Creation of the Cost Model]
-}
main :: IO ()
main = do
  model <- createBuiltinCostModel
  BSL.writeFile builtinCostModelFile $ encodePretty' (defConfig { confCompare = \_ _-> EQ }) model
