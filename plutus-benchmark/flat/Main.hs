{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import           Codec.Serialise        (Serialise)
import           Control.DeepSeq        (NFData, force)
import           Criterion.Main
import           Criterion.Types
import qualified Data.ByteString        as BS
import           Data.Map.Strict        (Map, fromList, lookup)
import           Data.Maybe             (fromJust)
import           Data.Text              (Text, unpack)
import           Flat                   (Flat)
import           Paths_plutus_benchmark (getDataFileName)
import           System.FilePath
import           UntypedPlutusCore

import           Codec
import           Dataset
import           Report

import           Prelude                hiding (lookup)

-- | A list of all contracts serialized using all codecs.
serializedContracts :: Map (Text, Text) BS.ByteString
serializedContracts = fromList $
  concatMap serializeContract contractsWithNames ++
  concatMap serializeContract contractsWithIndices
  where
    serializeContract :: (Flat a, Flat (Binder a), Serialise a)
                      => (Text, Tm a)
                      -> [((Text, Text), BS.ByteString)]
    serializeContract (name, tm) = do
      map (\(cName, codec) -> ((name, cName), serialize codec tm)) codecs

-- | Benchmark contract serialization for a specific contract using a specific codec.
benchmarkSerialize ::
     (Text, Tm a)
  -> (Text, Codec (Tm a))
  -> Benchmark
benchmarkSerialize (contractName, contract) (codecName, codec) =
  bench (unpack $ " " <> contractName <> " - " <> codecName)
        (nf (serialize codec) contract)

-- | Benchmark contract de-serialization for a contract/codec combination.
benchmarkDeserialize ::
     NFData a
  => Map (Text, Text) BS.ByteString
  -> (Text, Tm a)
  -> (Text, Codec (Tm a))
  -> Benchmark
benchmarkDeserialize scs (contractName, _) (codecName, codec) =
  -- Skip contract serialization when benchmarking deserialize
  let !serialized = fromJust $ lookup (contractName, codecName) scs
  in  bench (unpack $ " " <> contractName <> " - " <> codecName)
            (nf (Codec.deserialize codec) serialized)

{- | The Criterion configuration returned by `getConfig` will cause an HTML report
   to be generated.  If run via stack/cabal this will be written to the
   `plutus-benchmark` directory by default.  The -o option can be used to change
   this, but an absolute path will probably be required (eg,
   "-o=$PWD/report.html") . -}
getConfig :: IO Config
getConfig = do
  templateDir <- getDataFileName "templates"
  let templateFile = templateDir </> "with-iterations" <.> "tpl" -- Include number of iterations in HTML report
  pure $ defaultConfig {
                template = templateFile,
                reportFile = Just "flat-report.html"
              }

-- | Benchmarks for a contract.
benchmarkContracts ::
     NFData a
  => Map (Text, Text) BS.ByteString
  -> [(Text, Codec (Tm a))]
  -> [(Text, Tm a)]
  -> [Benchmark]
benchmarkContracts scs codecs' = concatMap $ \contract ->
  [ bgroup "serialization time " $
       map (benchmarkSerialize contract) codecs'
   , bgroup "deserialization time " $
       map (benchmarkDeserialize scs contract) codecs'
  ]

benchmarkConfig :: Config
benchmarkConfig = defaultConfig
  { reportFile = Just "flat-report.html" }

sizesReport :: FilePath
sizesReport = "flat-sizes.txt"

main :: IO ()
main = do
  {- We preload the contracts and serialize them outside of the benchmark. This
     will not put undue pressure on the memory since the serialized contracts
     are not large enough to warrant lazily loading them. -}
  let !scs = force serializedContracts
      !contractsWithNames' = force contractsWithNames
      !contractsWithIndices' = force contractsWithIndices
  config <- getConfig
  defaultMainWith config $
    benchmarkContracts scs codecs contractsWithNames' ++
    benchmarkContracts scs codecs contractsWithIndices'
  putStrLn $ "Measuring sizes (output to: " <> sizesReport <> ") ..."
  let szMeasures = withRatio . measureSize $ scs
  writeFile sizesReport (unpack . showContractMeasures $ szMeasures)
