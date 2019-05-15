-- | Contract interface for the crowdfunding contract
module Main where

import           Examples.Crowdfunding        (crowdfunding)
import qualified Language.Plutus.Contract.App as App

main :: IO ()
main = App.run crowdfunding
