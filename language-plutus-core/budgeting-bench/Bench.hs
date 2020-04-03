{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MagicHash #-}

module Main (main) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant.Dynamic
import           Language.PlutusCore.Evaluation.Machine.Cek
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import           Language.PlutusCore.Generators.Interesting
import Language.PlutusCore.FsTree
import Language.PlutusCore.MkPlc
import GHC.Integer.Logarithms
import GHC.Integer

import           Criterion.Main
import qualified Criterion.Types as C
import Control.Lens

runTermBench :: String -> Plain Term DefaultUni -> Benchmark
runTermBench name term = env
    (do 
        (result, budget) <-
          pure $ runCekCounting mempty defaultCostingFunParameters term
        -- print result
        print (budget ^. (exBudgetStateBudget.exBudgetCPU) :: ExCPU)
        pure budget
        )
    (\_ -> bench name $ nf (unsafeEvaluateCek mempty defaultCostingFunParameters) term)

bunchOfFibs :: PlcFolderContents DefaultUni
bunchOfFibs =
    let
        fibFile i = plcTermFile (show i) (naiveFib i)
    in
        FolderContents [ treeFolderContents "Fib" (fibFile <$> [1..10]) ]

twoIntTerm :: BuiltinName -> Integer -> Integer -> Plain Term DefaultUni
twoIntTerm name x y =
    mkIterApp ()
        (builtin () $ BuiltinName () name)
        [(mkConstant () x), (mkConstant () y)]

expsToBench :: [Integer]
expsToBench = ((\(a :: Integer) -> 2^a) <$> [1..9]) <> ((\(a :: Integer) -> 10^a) <$> [3..8])

benchTwoInt :: BuiltinName -> [(String, Plain Term DefaultUni)]
benchTwoInt name = do
    x_exp :: Integer <- expsToBench
    let
        x = ((3 :: Integer) ^ x_exp)
        xCeilSize = smallInteger (integerLog2# x)
    y_exp :: Integer <- expsToBench
    let
        y = ((3 :: Integer) ^ y_exp)
        yCeilSize = smallInteger (integerLog2# y)
    pure $ (
        show name <> ": 3^" <> show x_exp <> " (" <> ", " <> show xCeilSize <> "), 3^" <> show y_exp <> " (" <> show yCeilSize <> ")",
        twoIntTerm name x y)

calibratingBench :: Benchmark
calibratingBench =
    env
        (pure $ mkConstant @Integer @DefaultUni () 0)
        (\x -> bench "calibration" $ nf (unsafeEvaluateCek @DefaultUni mempty defaultCostingFunParameters) x)

main :: IO ()
main = do
    let twoInt name = ((uncurry runTermBench) <$> benchTwoInt name)
    let twoIntNames = [AddInteger, SubtractInteger, MultiplyInteger, DivideInteger, QuotientInteger, RemainderInteger, ModInteger, LessThanInteger, LessThanEqInteger, GreaterThanEqInteger, GreaterThanEqInteger, EqInteger]
    -- let twoIntNames = [MultiplyInteger]
    -- _ <- CP.try @CP.SomeException $ removeFile "output.csv" -- because otherwise benching will append to the old csv
    -- TODO remove the time limit
    defaultMainWith (defaultConfig { C.csvFile = Just "output.csv" }) $ twoIntNames >>= twoInt
{-       foldPlcFolderContents
        bgroup
        (\name _ -> bgroup name [])
        runTermBench
        bunchOfFibs -}

{-     [ env largeTypeFiles $ \ ~(f, g, h) ->
                    let mkBench = bench "pretty" . nf (fmap prettyPlcDefText) . parse
                    in

                    bgroup "prettyprint" $ mkBench <$> [f, g, h]
                ] -}