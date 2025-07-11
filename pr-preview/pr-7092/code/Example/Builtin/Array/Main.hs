{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:target-version=1.1.0 #-}

module Main where

import Colourista (black, bold, formattedMessage, greenBg, magentaBg, white)
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.IO qualified as Text
import PlutusCore.Evaluation.Machine.ExBudget (ExBudget (..))
import PlutusCore.Evaluation.Machine.ExMemory (CostingInteger, ExCPU (..), ExMemory (..))
import PlutusTx qualified as Plinth
import PlutusTx.BuiltinList (BuiltinList)
import PlutusTx.BuiltinList qualified as BuiltinList
import PlutusTx.Builtins (BuiltinArray, indexArray, sopListToArray, toOpaque)
import PlutusTx.List qualified as SOP
import PlutusTx.Test.Run.Code (EvalResult (..), displayExBudget, evaluateCompiledCode)
import Text.Printf (printf)
import Unsafe.Coerce (unsafeCoerce)

--------------------------------------------------------------------------------
-- Plinth ----------------------------------------------------------------------

usesSopList :: Plinth.CompiledCode Integer
usesSopList =
  $$(Plinth.compile [||lookupByIndex sopListOfInts||])
 where
  lookupByIndex :: [Integer] -> Integer
  lookupByIndex xs = xs SOP.!! 99

usesBuiltinList :: Plinth.CompiledCode Integer
usesBuiltinList =
  $$(Plinth.compile [||lookupByIndex (toOpaque sopListOfInts)||])
 where
  lookupByIndex :: BuiltinList Integer -> Integer
  lookupByIndex xs = xs BuiltinList.!! 99

usesArray :: Plinth.CompiledCode Integer
usesArray =
  $$(Plinth.compile [||lookupByIndex (sopListToArray sopListOfInts)||])
 where
  lookupByIndex :: BuiltinArray Integer -> Integer
  lookupByIndex xs = indexArray xs 99

sopListConstruction :: Plinth.CompiledCode [Integer]
sopListConstruction = $$(Plinth.compile [||sopListOfInts||])

builtinListConstruction :: Plinth.CompiledCode (BuiltinList Integer)
builtinListConstruction = $$(Plinth.compile [||toOpaque sopListOfInts||])

builtinArrayConstruction :: Plinth.CompiledCode (BuiltinArray Integer)
builtinArrayConstruction = $$(Plinth.compile [||sopListToArray sopListOfInts||])

{- FOURMOLU_DISABLE -}
sopListOfInts :: [Integer]
sopListOfInts =
  [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28
  ,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53
  ,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78
  ,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99
  ]
{- FOURMOLU_ENABLE -}

builtinListOfInts :: BuiltinList Integer
builtinListOfInts = toOpaque sopListOfInts

--------------------------------------------------------------------------------
-- Main ------------------------------------------------------------------------

main :: IO ()
main = do
  printHeader greenBg "SOP List"

  printSubHeader "Construction"
  let sopListConstructionResult = evaluateCompiledCode sopListConstruction
      sopListConstructionBudget = evalResultBudget sopListConstructionResult
  printBudget sopListConstructionBudget

  printSubHeader "Lookup"
  let sopListTotalBudget =
        -- Total means construction + lookup
        evalResultBudget (evaluateCompiledCode usesSopList)
      sopListLookupBudget =
        sopListTotalBudget `subtractBudget` sopListConstructionBudget
  printBudget sopListLookupBudget

  printSubHeader "Construction + Lookup"
  printBudget sopListTotalBudget

  printHeader greenBg "Builtin List"

  printSubHeader "Construction"
  let builtinListConstructionResult =
        evaluateCompiledCode builtinListConstruction
      builtinListConstructionBudget =
        evalResultBudget builtinListConstructionResult
  printBudget builtinListConstructionBudget

  printSubHeader "Lookup"
  let builtinListLookupEvalResult = evaluateCompiledCode usesBuiltinList
      builtinListTotalBudget =
        evalResultBudget builtinListLookupEvalResult
      builtinListLookupBudget =
        builtinListTotalBudget `subtractBudget` builtinListConstructionBudget
  printBudget builtinListLookupBudget

  printSubHeader "Construction + Lookup"
  printBudget builtinListTotalBudget

  printHeader greenBg "Builtin Array"

  printSubHeader "Construction"
  let arrayConstructionEvalResult =
        evaluateCompiledCode builtinArrayConstruction
      arrayConstructionBudget =
        evalResultBudget arrayConstructionEvalResult
  printBudget arrayConstructionBudget

  printSubHeader "Lookup"
  let builtinArrayTotalEvalResult = evaluateCompiledCode usesArray
      builtinArrayTotalBudget = evalResultBudget builtinArrayTotalEvalResult
      builtinArrayLookupBudget =
        builtinArrayTotalBudget `subtractBudget` arrayConstructionBudget
  printBudget builtinArrayLookupBudget

  printSubHeader "Construction + Lookup"
  printBudget builtinArrayTotalBudget

  printHeader magentaBg "SOP List vs. Builtin List"
  printPercentage sopListLookupBudget builtinListLookupBudget

  printHeader magentaBg "SOP List vs. BuiltinArray"
  printPercentage sopListLookupBudget builtinArrayLookupBudget

  printHeader magentaBg "BuiltinList vs. BuiltinArray"
  printPercentage builtinListLookupBudget builtinArrayLookupBudget

  printSubHeader "Legend"
  putStrLn
    "A negative percentage indicates that \
    \cost is lower on the right hand side of a comparison."
  putStrLn "\n"

--------------------------------------------------------------------------------
-- Helper Functions ------------------------------------------------------------

printHeader :: Text -> Text -> IO ()
printHeader bg x = do
  putStrLn ""
  formattedMessage [bold, bg, black] (" " <> Text.strip x <> " ")

printSubHeader :: Text -> IO ()
printSubHeader x = formattedMessage [bold, white] ("\n" <> x)

printBudget :: ExBudget -> IO ()
printBudget = Text.putStrLn . displayExBudget

printPercentage :: ExBudget -> ExBudget -> IO ()
printPercentage oldResult newResult = do
  let (cpuOld, memOld) = evalResultToCpuMem oldResult
      (cpuNew, memNew) = evalResultToCpuMem newResult
  putStr "CPU change: "
  putStrLn $ improvementPercentage cpuOld cpuNew
  putStr "MEM change: "
  putStrLn $ improvementPercentage memOld memNew
 where
  improvementPercentage :: Double -> Double -> String
  improvementPercentage old new =
    printf "%+.2f" ((new - old) / old * 100.0) <> " %"

  evalResultToCpuMem :: ExBudget -> (Double, Double)
  evalResultToCpuMem
    ExBudget
      { exBudgetCPU = ExCPU cpu
      , exBudgetMemory = ExMemory mem
      } = (toDouble cpu, toDouble mem)
     where
      toDouble :: CostingInteger -> Double
      toDouble x = fromIntegral (unsafeCoerce x :: Int)

subtractBudget :: ExBudget -> ExBudget -> ExBudget
subtractBudget
  ExBudget{exBudgetCPU = ExCPU cpu1, exBudgetMemory = ExMemory mem1}
  ExBudget{exBudgetCPU = ExCPU cpu2, exBudgetMemory = ExMemory mem2} =
    ExBudget (ExCPU (cpu1 - cpu2)) (ExMemory (mem1 - mem2))
