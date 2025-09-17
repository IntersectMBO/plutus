{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings         #-}

module PlutusCore.Flat.Test.Main where

import Data.List (isSuffixOf)
import Data.Text qualified as T
import System.Environment
import System.FilePath.Find
import Test.DocTest (doctest, genTests)
t = main

{-
Note: Some doctests won't compile with ghc 7.10.3 (as they use TypeApplication syntax)
-}

-- e.g.: stack test :doc --file-watch --fast --test-arguments="Data.ZigZag Flat.Instances Flat.Instances.Base"
main :: IO ()
main = do
  args  <- getArgs
  -- print args
  files <- if not (null args)
    then return $ map
      ( T.unpack
      . (`T.append` ".hs")
      . ("src/" `T.append`)
      . T.replace "." "/"
      . T.pack
      )
      args
    else find always ((extension ==? ".hs") &&? exceptFiles []) "src"
  -- print files
  runTests runOpts files
  genTests genOpts files

runTests opts files = doctest $ opts ++ files

runOpts = ["--fast", "-XCPP","--verbose"]

-- static tests are generated with ghcjs compatibility as they cannot be generated in ghcjs
-- but this creates trouble with imports
-- genOpts = runOpts ++ ["-Dghcjs_HOST_OS"]
-- genOpts = runOpts ++ ["-Dghcjs_HOST_OS", "-DETA"]
genOpts = runOpts

exceptFiles :: Foldable t => t String -> FindClause Bool
exceptFiles mdls =
  let excludes = liftOp (\fp modules -> not $ any (`isSuffixOf` fp) modules)
  in  filePath `excludes` mdls
-- let excludes = liftOp (\fp mdls -> not $ any (\mdl -> isSuffixOf mdl (traceShowId fp)) mdls)
