module Main where

import           Data.Aeson.Encode.Pretty
import qualified Data.ByteString.Lazy     as BSL

import           CostModelCreation

{- See Note [Creation of the Cost Model]
-}
main :: IO ()
main = do
  model <- createCostModel
  BSL.writeFile "cost-model/data/builtinCostModel.json" $ encodePretty' (defConfig { confCompare = \_ _-> EQ }) model
