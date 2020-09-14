{-# LANGUAGE OverloadedStrings #-}
module Main(main) where

import qualified Spec.Marlowe.Marlowe
import           Test.Tasty

main :: IO ()
main = defaultMain Spec.Marlowe.Marlowe.tests
