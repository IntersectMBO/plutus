module Main where

import           Data.Aeson.Encode.Pretty
import qualified Data.ByteString.Lazy     as BSL

import           CostModelCreation

{- See Note [Creation of the Cost Model]
-}
main :: IO ()
main = do
  model <- createCostModel
  BSL.writeFile "plutus-core/src/costModel.json" $ encodePretty' (defConfig { confCompare = \_ _-> EQ }) model
