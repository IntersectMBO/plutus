{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

-- See Note [Creation of the Cost Model]
module Main (main) where

import           Language.PlutusCore                                as PLC
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import           Language.PlutusCore.MkPlc
import           Language.UntypedPlutusCore                         as UT
import           Language.UntypedPlutusCore.Evaluation.Machine.Cek

import           Criterion.Main
import qualified Criterion.Types                                    as C
import qualified Data.ByteString                                    as BS
import           Data.Functor
import qualified Data.Kind                                          as GHC
import           Hedgehog
import           Hedgehog.Internal.Gen
import           Hedgehog.Internal.Tree
import           Hedgehog.Range
import           System.Directory
import           System.FilePath

type UntypedPlain f (uni :: GHC.Type -> GHC.Type) (fun :: GHC.Type) = f Name uni fun ()

runTermBench :: String -> UntypedPlain UT.Term DefaultUni DefaultFun -> Benchmark
runTermBench name term = env
    (do
        (_result, budget) <-
          pure $ runCekNoEmit defBuiltinsRuntime Counting term
        pure budget
        )
    (\_ -> bench name $ nf (unsafeEvaluateCek defBuiltinsRuntime) term)

-- Copying the bytestring here, because otherwise it'll be exactly the same, and the equality will short-circuit.
benchSameTwoByteStrings :: DefaultFun -> Benchmark
benchSameTwoByteStrings name = createTwoTermBuiltinBench name (byteStringsToBench seedA) ((\(bs, e) -> (BS.copy bs, e)) <$> byteStringsToBench seedA)

benchTwoByteStrings :: DefaultFun -> Benchmark
benchTwoByteStrings name = createTwoTermBuiltinBench name (byteStringsToBench seedA) (byteStringsToBench seedB)

benchBytestringOperations :: DefaultFun -> Benchmark -- TODO the numbers are a bit too big here
benchBytestringOperations name = createTwoTermBuiltinBench @Integer @BS.ByteString name numbers (byteStringsToBench seedA)
    where
        numbers = expToBenchingInteger <$> expsToBench

createTwoTermBuiltinBench
    :: (DefaultUni `Includes` a, DefaultUni `Includes` b)
    => DefaultFun
    -> [(a, ExMemory)]
    -> [(b, ExMemory)]
    -> Benchmark
createTwoTermBuiltinBench name as bs =
    bgroup (show name) $
        as <&> (\(x, xMem) ->
            bgroup (show xMem) $ bs <&> (\(y, yMem) ->
                runTermBench (show yMem) $ erase $
                             mkIterApp () (builtin () name) [mkConstant () x,  mkConstant () y]
            ))

benchComparison :: [Benchmark]
benchComparison = (\n -> runTermBench ("CalibratingBench/ExMemory " <> show n) (erase $ createRecursiveTerm n)) <$> [1..20]

-- Creates a cheap builtin operation to measure the base cost of executing one.
createRecursiveTerm :: Integer -> Plain PLC.Term DefaultUni DefaultFun
createRecursiveTerm d = mkIterApp () (builtin () AddInteger)
                        [ (mkConstant () (1::Integer))
                        , if d == 0
                          then mkConstant () (1::Integer)
                          else createRecursiveTerm (d - 1)
                        ]

benchHashOperations :: DefaultFun -> Benchmark
benchHashOperations name =
    bgroup (show name) $
        byteStringsToBench seedA <&> (\(x, xMem) ->
            runTermBench (show xMem) $ erase $ mkIterApp () (builtin () name) [(mkConstant () x)]
        )

-- for VerifySignature, for speed purposes, it shouldn't matter if the sig / pubkey are correct
sig :: BS.ByteString
sig = "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b"
pubKey :: BS.ByteString
pubKey = "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"
benchVerifySignature :: Benchmark
benchVerifySignature =
    bgroup (show name) $
        bs <&> (\(x, xMem) ->
            runTermBench (show xMem) $ erase $
                         mkIterApp () (builtin () name)
                         [ mkConstant () pubKey
                         , mkConstant () x
                         , mkConstant () sig
                         ]
        )
    where
        name = VerifySignature
        bs = (expToBenchingBytestring seedA . fromInteger) <$> expsToBenchBS

expsToBenchBS :: [Integer]
expsToBenchBS = ((\(a :: Integer) -> 2^a) <$> [1..20])

byteStringsToBench :: Seed -> [(BS.ByteString, ExMemory)]
byteStringsToBench seed = (expToBenchingBytestring seed . fromInteger) <$> expsToBenchBS

expsToBench :: [Integer]
expsToBench = ((\(a :: Integer) -> 2^a) <$> [1..16]) -- <> ((\(a :: Integer) -> 10^a) <$> [3..8])

seedA :: Seed
seedA = (Seed 42 43)
seedB :: Seed
seedB = (Seed 44 45)

genSample :: Seed -> Gen a -> a
genSample seed gen = Prelude.maybe (Prelude.error "Couldn't create a sample") treeValue $ evalGen (Size 1) seed gen

-- TODO make a nice class out of these
expToBenchingBytestring :: Seed -> Int -> (BS.ByteString, ExMemory)
expToBenchingBytestring seed e = let x = genSample seed (bytes (Hedgehog.Range.singleton e)) in (x, memoryUsage x)

-- TODO make the e the actual ExMemory size
expToBenchingInteger :: Integer -> (Integer, ExMemory)
expToBenchingInteger e =
            let
                x = (3 :: Integer) ^ e
            in (x, memoryUsage x)

benchTwoInt :: DefaultFun -> Benchmark
benchTwoInt builtinName =
    createTwoTermBuiltinBench builtinName numbers numbers
    where
        numbers = expToBenchingInteger <$> expsToBench

-- Creates the .csv file consumed by create-cost-model. The data in said csv is
-- time taken for all the builtin operations, as measured by criterion.
-- See also Note [Creation of the Cost Model]
--
-- TODO: Some care is required here regarding the current working directory.  If
-- you run this benchmark via `cabal bench` or `stack bench` (but not `cabal
-- run`) then the current directory will be `plutus-core`.  If you use nix it'll
-- be the current shell directory, so you'll need to run it from `plutus-core`
-- (NOT `plutus`, where `default.nix` is).  See SCP-2005.
main :: IO ()
main = do
  let dataDir = "cost-model" </> "data"
      csvFile = dataDir </> "benching.csv"
      backupFile = dataDir </> "benching.csv.backup"
  createDirectoryIfMissing True dataDir
  csvExists <- doesFileExist csvFile
  if csvExists then renameFile csvFile backupFile else pure ()

  defaultMainWith (defaultConfig { C.csvFile = Just csvFile })
                        $  (benchTwoInt <$> twoIntNames)
                        <> (benchTwoByteStrings <$> [Concatenate])
                        <> (benchBytestringOperations <$> [DropByteString, TakeByteString])
                        <> (benchHashOperations <$> [SHA2, SHA3])
                        <> (benchSameTwoByteStrings <$> [EqByteString, LtByteString, GtByteString])
                        <> [benchVerifySignature]
                        <> benchComparison
  pure ()
    where twoIntNames = [ AddInteger, SubtractInteger, MultiplyInteger, DivideInteger
                        , QuotientInteger, RemainderInteger, ModInteger, LessThanInteger
                        , LessThanEqInteger, GreaterThanInteger, GreaterThanEqInteger, EqInteger]
