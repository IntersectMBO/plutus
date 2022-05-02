{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Data.Text.IO (readFile)
import Prelude hiding (readFile)
import Test.Tasty.Golden (findByExtension)

main :: IO ()
main = do
    inputFiles <- findByExtension [".plc"] "tplc/typecheck/"
    outputFiles <- findByExtension [".expected"] "tplc/typecheck/"
    _lProg <- traverse readFile inputFiles
    _lTcRes <- traverse readFile outputFiles
    pure ()

