{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Main (main) where

import           Language.PlutusCore
-- import           Language.PlutusCore.Constant.Dynamic
import           Language.PlutusCore.Evaluation.Machine.Cek
-- import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import           Language.PlutusCore.Evaluation.Machine.ExMemory
-- import           Language.PlutusCore.Evaluation.Machine.ExMemory
-- import           Language.PlutusCore.FsTree
-- import           Language.PlutusCore.Generators.Interesting
import qualified Data.ByteString.Lazy                                       as BSL
import           Hedgehog
import           Hedgehog.Internal.Gen
import           Hedgehog.Internal.Tree
import           Hedgehog.Range
import           Language.PlutusCore.MkPlc

-- import           Control.Lens
import           Criterion.Main
import qualified Criterion.Types                                            as C
import Data.Functor

runTermBench :: String -> Plain Term DefaultUni -> Benchmark
runTermBench name term = env
    (do
        (_result, budget) <-
          pure $ runCekCounting mempty defaultCostModel term
        -- print result
        -- print (budget ^. (exBudgetStateBudget.exBudgetCPU) :: ExCPU)
        pure budget
        )
    (\_ -> bench name $ nf (unsafeEvaluateCek mempty defaultCostModel) term)

-- bunchOfFibs :: PlcFolderContents DefaultUni
-- bunchOfFibs =
--     let
--         fibFile i = plcTermFile (show i) (naiveFib i)
--     in
        -- FolderContents [ treeFolderContents "Fib" (fibFile <$> [1..10]) ]

benchSameTwoByteStrings :: BuiltinName -> Benchmark
benchSameTwoByteStrings name = createTwoTermBuiltinBench name (byteStringsToBench seedA) (byteStringsToBench seedA)

benchTwoByteStrings :: BuiltinName -> Benchmark
benchTwoByteStrings name = createTwoTermBuiltinBench name (byteStringsToBench seedA) (byteStringsToBench seedB)

benchBytestringOperations :: BuiltinName -> Benchmark -- TODO the numbers are a bit too big here
benchBytestringOperations name = createTwoTermBuiltinBench @Integer @BSL.ByteString name numbers (byteStringsToBench seedA)
    where
        numbers = expToBenchingInteger <$> expsToBench

createTwoTermBuiltinBench :: (DefaultUni `Includes` a, DefaultUni `Includes` b) => BuiltinName -> [(a, ExMemory)] -> [(b, ExMemory)] -> Benchmark
createTwoTermBuiltinBench name as bs =
    bgroup (show name) $
        as <&> (\(x, xMem) ->
            bgroup (show xMem) $ bs <&> (\(y, yMem) ->
                runTermBench (show yMem) $ mkIterApp () (builtin () $ BuiltinName () name) [(mkConstant () x), (mkConstant () y)]
            ))

benchHashOperations :: BuiltinName -> Benchmark
benchHashOperations name =
    bgroup (show name) $
        byteStringsToBench seedA <&> (\(x, xMem) ->
            runTermBench (show xMem) $ mkIterApp () (builtin () $ BuiltinName () name) [(mkConstant () x)]
        )

-- for VerifySignature, for speed purposes, it shouldn't matter if the sig / pubkey are correct
sig :: BSL.ByteString
sig = "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b"
pubKey :: BSL.ByteString
pubKey = "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"
benchVerifySignature :: Benchmark
benchVerifySignature =
    bgroup (show name) $
        bs <&> (\(x, xMem) ->
            runTermBench (show xMem) $ mkIterApp () (builtin () $ BuiltinName () name) [(mkConstant () pubKey), (mkConstant () x), (mkConstant () sig)]
        )
    where
        name = VerifySignature
        bs = (expToBenchingBytestring seedA . fromInteger) <$> expsToBench

expsToBenchBS :: [Integer]
expsToBenchBS = ((\(a :: Integer) -> 1^a) <$> [1..9]) <> ((\(a :: Integer) -> 10^a) <$> [3..7])

byteStringsToBench :: Seed -> [(BSL.ByteString, ExMemory)]
byteStringsToBench seed = (expToBenchingBytestring seed . fromInteger) <$> expsToBenchBS

expsToBench :: [Integer]
expsToBench = ((\(a :: Integer) -> 2^a) <$> [1..9]) <> ((\(a :: Integer) -> 10^a) <$> [3..8])

seedA :: Seed
seedA = (Seed 42 43)
seedB :: Seed
seedB = (Seed 44 45)

genSample :: Seed -> Gen a -> a
genSample seed gen = Prelude.maybe (Prelude.error "Couldn't create a sample") treeValue $ evalGen (Size 1) seed gen

-- TODO make a nice class out of these
expToBenchingBytestring :: Seed -> Int -> (BSL.ByteString, ExMemory)
expToBenchingBytestring seed e = let x = BSL.fromStrict $ genSample seed (bytes (Hedgehog.Range.singleton e)) in (x, memoryUsage x)

-- TODO make the e the actual ExMemory size
expToBenchingInteger :: Integer -> (Integer, ExMemory)
expToBenchingInteger e =
            let
                x = ((3 :: Integer) ^ e)
                -- ceilSize = smallInteger (integerLog2# x)
            in (x, memoryUsage x)

benchTwoInt :: BuiltinName -> Benchmark
benchTwoInt builtinName =
    createTwoTermBuiltinBench builtinName numbers numbers
    where
        numbers = expToBenchingInteger <$> expsToBench

-- calibratingBench :: Benchmark
-- calibratingBench =
--     env
--         (pure $ mkConstant @Integer @DefaultUni () 0)
--         (\x -> bench "calibration" $ nf (unsafeEvaluateCek @DefaultUni mempty defaultCostModel) x)

main :: IO ()
main = do
    -- let twoIntNames = [MultiplyInteger]
    -- _ <- CP.try @CP.SomeException $ removeFile "output.csv" -- because otherwise benching will append to the old csv
    -- TODO remove the time limit
    -- parFoldMap (Simple Terminate) 5 runBuiltinBench mappend mempty twoIntNames
    -- benchToRun <- execParser $ info (p <**> helper) fullDesc
    -- runBuiltinBench benchToRun
    defaultMainWith (defaultConfig { C.csvFile = Just $ "language-plutus-core/budgeting-bench/csvs/benching.csv" }) $ (benchTwoInt <$> twoIntNames) <> (benchTwoByteStrings <$> [LtByteString, GtByteString, Concatenate]) <> (benchBytestringOperations <$> [DropByteString, TakeByteString]) <> (benchHashOperations <$> [SHA2, SHA3]) <> (benchSameTwoByteStrings <$> [EqByteString]) <> [benchVerifySignature]
    pure ()
    where
        twoIntNames = [AddInteger, SubtractInteger, MultiplyInteger, DivideInteger, QuotientInteger, RemainderInteger, ModInteger, LessThanInteger, LessThanEqInteger, GreaterThanEqInteger, GreaterThanEqInteger, EqInteger]
        -- parseTwoIntName string = lookup string ((\n -> (show n, n)) <$> twoIntNames)
        -- p :: Parser BuiltinName
        -- p = option (maybeReader parseTwoIntName) (long "toRun")
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
