module Main where

import           Default
import           Expr
import           NonDefault
import           Universal

import           Build_doctests     (flags, module_sources, pkgs)
import           System.Environment (unsetEnv)
import           Test.DocTest       (doctest)
import           Test.Tasty

main :: IO ()
main = do
    unsetEnv "GHC_ENVIRONMENT"
    doctest $ flags ++ pkgs ++ module_sources
    defaultMain $ testGroup "all"
        [ test_default
        , test_nonDefault
        , test_universal
        , test_expr
        ]
