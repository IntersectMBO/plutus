module Main where

import           Default
import           Expr
import           NonDefault
import           Universal

import           Build_doctests     (flags, module_sources, pkgs)
import           System.Environment (unsetEnv)
import           Test.DocTest       (doctest)
import           Test.Tasty
import           Test.Tasty.HUnit   (testCase)

main :: IO ()
main = do
    -- @cabal-doctest@ docs suggest doing that. No idea if it's required.
    unsetEnv "GHC_ENVIRONMENT"
    defaultMain $ testGroup "all"
        [ -- Pretending all doctests are a single unit test.
          testCase "doctests" . doctest $ flags ++ pkgs ++ module_sources
        , test_default
        , test_nonDefault
        , test_universal
        , test_expr
        ]
