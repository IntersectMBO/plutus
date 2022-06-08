module Main (main) where

import Common (evalUplcProg, runTests)
import Prelude hiding (readFile)

main :: IO ()
main = runTests evalUplcProg

