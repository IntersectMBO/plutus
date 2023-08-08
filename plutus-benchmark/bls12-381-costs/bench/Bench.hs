-- editorconfig-checker-disable-file
{- | Plutus benchmarks measuring actual execution times of some BSL12-381
   operations, mainly intended to give us an idea of what we can do within the
   on-chain execution limits. -}
module Main where

import Criterion.Main

import PlutusBenchmark.BLS12_381.Scripts
import PlutusBenchmark.Common (benchTermCek)
import PlutusTx.Prelude qualified as Tx
import UntypedPlutusCore qualified as UPLC

import Data.ByteString qualified as BS (empty)

benchProgCek :: UPLC.Program UPLC.NamedDeBruijn UPLC.DefaultUni UPLC.DefaultFun ()  -> Benchmarkable
benchProgCek (UPLC.Program _ _ t) = benchTermCek t

benchHashAndAddG1 :: Integer -> Benchmark
benchHashAndAddG1 n =
    let prog = mkHashAndAddG1Script (listOfSizedByteStrings n 4)
    in bench (show n) $ benchProgCek prog

benchHashAndAddG2 :: Integer -> Benchmark
benchHashAndAddG2 n =
    let prog = mkHashAndAddG2Script (listOfSizedByteStrings n 4)
    in bench (show n) $ benchProgCek prog

benchUncompressAndAddG1 :: Integer -> Benchmark
benchUncompressAndAddG1 n =
    let prog = mkUncompressAndAddG1Script (listOfSizedByteStrings n 4)
    in bench (show n) $ benchProgCek prog

benchUncompressAndAddG2 :: Integer -> Benchmark
benchUncompressAndAddG2 n =
    let prog = mkUncompressAndAddG2Script (listOfSizedByteStrings n 4)
    in bench (show n) $ benchProgCek prog

benchPairing :: Benchmark
benchPairing =
    case listOfSizedByteStrings 4 4 of
      [b1, b2, b3, b4] ->
          let emptyDst = Tx.toBuiltin BS.empty
              p1 = Tx.bls12_381_G1_hashToGroup (Tx.toBuiltin b1) emptyDst
              p2 = Tx.bls12_381_G2_hashToGroup (Tx.toBuiltin b2) emptyDst
              q1 = Tx.bls12_381_G1_hashToGroup (Tx.toBuiltin b3) emptyDst
              q2 = Tx.bls12_381_G2_hashToGroup (Tx.toBuiltin b4) emptyDst
              prog = mkPairingScript p1 p2 q1 q2
          in bench "pairing" $ benchProgCek prog
      _ -> error "Unexpected list returned by listOfSizedByteStrings"

benchGroth16Verify :: Benchmark
benchGroth16Verify = bench "groth16Verify" $ benchProgCek mkGroth16VerifyScript

benchSimpleVerify :: Benchmark
benchSimpleVerify = bench "simpleVerify" $ benchProgCek mkVerifyBlsSimplePolicy

benchVrf :: Benchmark
benchVrf = bench "vrf" $ benchProgCek mkVrfBlsPolicy

benchG1Verify :: Benchmark
benchG1Verify = bench "g1Verify" $ benchProgCek mkG1VerifyPolicy

benchG2Verify :: Benchmark
benchG2Verify = bench "g2Verify" $ benchProgCek mkG2VerifyPolicy

aggregateSigSingleKey :: Benchmark
aggregateSigSingleKey = bench "aggregateSignatureSingleKey" $ benchProgCek mkAggregateSingleKeyG1Policy

aggregateSigMultiKey :: Benchmark
aggregateSigMultiKey = bench "aggregateSignatureMultiKey" $ benchProgCek mkAggregateMultiKeyG2Policy

schnorrG1Verify :: Benchmark
schnorrG1Verify = bench "schnorrVerifyG1" $ benchProgCek mkSchnorrG1VerifyPolicy

schnorrG2Verify :: Benchmark
schnorrG2Verify = bench "schnorrVerifyG2" $ benchProgCek mkSchnorrG2VerifyPolicy

main :: IO ()
main = do
  defaultMain [
        bgroup "hashAndAddG1" $ fmap benchHashAndAddG1 [0, 10..150]
      , bgroup "hashAndAddG2" $ fmap benchHashAndAddG2 [0, 10..150]
      , bgroup "uncompressAndAddG1" $ fmap benchUncompressAndAddG1 [0, 10..150]
      , bgroup "uncompressAndAddG2" $ fmap benchUncompressAndAddG2 [0, 10..150]
      , benchPairing
      , benchGroth16Verify
      , benchSimpleVerify
      , benchVrf
      , benchG1Verify
      , benchG2Verify
      , aggregateSigSingleKey
      , aggregateSigMultiKey
      , schnorrG1Verify
      , schnorrG2Verify
       ]
