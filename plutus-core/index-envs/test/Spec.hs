module Main
    ( main
    ) where

import RAList.Spec qualified as RAList
import System.Environment.IgnoreAccept
import Test.Tasty

main :: IO ()
main = ignoreAcceptOption $ defaultMain RAList.tests
