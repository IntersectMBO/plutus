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
    if length inputFiles == length lProgTxt && length  lEvaluatedRes == length lProgTxt then
        do
        let lRes = fmap textToEvalRes lEvaluatedRes
            testContents = mkTestContents inputFiles lRes lProgTxt
        testTree <- testUplcEvaluation testContents evalUplcProg
        defaultMain testTree
    else
        error $ unlines
            ["Cannot run the tests because the number of input and output programs are not the same. "
            , "Number of input files: "
            , show (length lProgTxt)
            , " Number of output files: "
            , show (length lEvaluatedRes)
            , " Make sure all your input programs have an accompanying .expected file."
            ]
