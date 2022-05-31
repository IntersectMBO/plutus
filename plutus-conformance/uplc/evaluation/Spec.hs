{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Common (evalUplcProg, mkTestContents, testUplcEvaluation, textToEvalRes)
import Data.Text.IO (readFile)
import Prelude hiding (readFile)
import Test.Tasty (defaultMain)
import Test.Tasty.Golden (findByExtension)

main :: IO ()
main = do
    inputFiles <- findByExtension [".uplc"] "uplc/evaluation/"
    outputFiles <- findByExtension [".expected"] "uplc/evaluation/"
    lProgTxt <- traverse readFile inputFiles
    lEvaluatedRes <- traverse readFile outputFiles
    let lRes = fmap textToEvalRes lEvaluatedRes
        testContents = mkTestContents inputFiles lRes lProgTxt
    testTree <- testUplcEvaluation testContents evalUplcProg
    defaultMain testTree
