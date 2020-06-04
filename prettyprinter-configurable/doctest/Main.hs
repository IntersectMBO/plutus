module Main where

import           Build_doctests     (flags, module_sources, pkgs)
import           System.Environment (unsetEnv)
import           Test.DocTest       (doctest)

main :: IO ()
main = do
    -- @cabal-doctest@ docs suggest doing that. No idea if it's required.
    unsetEnv "GHC_ENVIRONMENT"
    doctest $ flags ++ pkgs ++ module_sources
