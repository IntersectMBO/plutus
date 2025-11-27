module Main
  ( main
  ) where

import RAList.Spec qualified as RAList
import Test.Tasty

main :: IO ()
main = defaultMain RAList.tests
