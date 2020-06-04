module Main where

import           Build_doctests     (flags, module_sources, pkgs)
import           System.Environment (unsetEnv)
import           Test.DocTest       (doctest)
import           Test.Tasty
import           Test.Tasty.HUnit   (testCase)

main :: IO ()
main = do
    -- @cabal-doctest@ docs suggest doing that. No idea if it's required.
    unsetEnv "GHC_ENVIRONMENT"
    -- Pretending all doctests are a single unit test.
    defaultMain $ testCase "doctests" . doctest $ flags ++ pkgs ++ module_sources
