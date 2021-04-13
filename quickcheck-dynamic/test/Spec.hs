{-# LANGUAGE OverloadedStrings #-}
module Main(main) where

import qualified Spec.DynamicLogic.RegistryModel
import           Test.Tasty

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "dynamic logic" [
    Spec.DynamicLogic.RegistryModel.tests
    ]
