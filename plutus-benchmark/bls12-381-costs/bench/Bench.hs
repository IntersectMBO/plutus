-- editorconfig-checker-disable-file

{-| Plutus benchmarks measuring actual execution times of some BSL12-381
   operations, mainly intended to give us an idea of what we can do within the
   on-chain execution limits. -}
module Main where

import Criterion.Main

import PlutusBenchmark.BLS12_381.Scripts
import PlutusBenchmark.Common (benchProgramCek, mkMostRecentEvalCtx)
import PlutusLedgerApi.Common (EvaluationContext)
import PlutusTx.Prelude qualified as Tx

import Control.Exception (evaluate)
import Data.ByteString qualified as BS (empty)

benchHashAndAddG1 :: EvaluationContext -> Integer -> Benchmark
benchHashAndAddG1 ctx n =
  let prog = mkHashAndAddG1Script (listOfByteStringsOfLength n 4)
   in bench (show n) $ benchProgramCek ctx prog

benchHashAndAddG2 :: EvaluationContext -> Integer -> Benchmark
benchHashAndAddG2 ctx n =
  let prog = mkHashAndAddG2Script (listOfByteStringsOfLength n 4)
   in bench (show n) $ benchProgramCek ctx prog

benchUncompressAndAddG1 :: EvaluationContext -> Integer -> Benchmark
benchUncompressAndAddG1 ctx n =
  let prog = mkUncompressAndAddG1Script (listOfByteStringsOfLength n 4)
   in bench (show n) $ benchProgramCek ctx prog

benchUncompressAndAddG2 :: EvaluationContext -> Integer -> Benchmark
benchUncompressAndAddG2 ctx n =
  let prog = mkUncompressAndAddG2Script (listOfByteStringsOfLength n 4)
   in bench (show n) $ benchProgramCek ctx prog

benchPairing :: EvaluationContext -> Benchmark
benchPairing ctx =
  case listOfByteStringsOfLength 4 4 of
    [b1, b2, b3, b4] ->
      let emptyDst = Tx.toBuiltin BS.empty
          p1 = Tx.bls12_381_G1_hashToGroup (Tx.toBuiltin b1) emptyDst
          p2 = Tx.bls12_381_G2_hashToGroup (Tx.toBuiltin b2) emptyDst
          q1 = Tx.bls12_381_G1_hashToGroup (Tx.toBuiltin b3) emptyDst
          q2 = Tx.bls12_381_G2_hashToGroup (Tx.toBuiltin b4) emptyDst
          prog = mkPairingScript p1 p2 q1 q2
       in bench "pairing" $ benchProgramCek ctx prog
    _ -> error "Unexpected list returned by listOfByteStringsOfLength"

benchGroth16Verify :: EvaluationContext -> Benchmark
benchGroth16Verify ctx = bench "groth16Verify" $ benchProgramCek ctx mkGroth16VerifyScript

benchSimpleVerify :: EvaluationContext -> Benchmark
benchSimpleVerify ctx = bench "simpleVerify" $ benchProgramCek ctx mkVerifyBlsSimplePolicy

benchVrf :: EvaluationContext -> Benchmark
benchVrf ctx = bench "vrf" $ benchProgramCek ctx mkVrfBlsPolicy

benchG1Verify :: EvaluationContext -> Benchmark
benchG1Verify ctx = bench "g1Verify" $ benchProgramCek ctx mkG1VerifyPolicy

benchG2Verify :: EvaluationContext -> Benchmark
benchG2Verify ctx = bench "g2Verify" $ benchProgramCek ctx mkG2VerifyPolicy

aggregateSigSingleKey :: EvaluationContext -> Benchmark
aggregateSigSingleKey ctx = bench "aggregateSignatureSingleKey" $ benchProgramCek ctx mkAggregateSingleKeyG1Policy

aggregateSigMultiKey :: EvaluationContext -> Benchmark
aggregateSigMultiKey ctx = bench "aggregateSignatureMultiKey" $ benchProgramCek ctx mkAggregateMultiKeyG2Policy

schnorrG1Verify :: EvaluationContext -> Benchmark
schnorrG1Verify ctx = bench "schnorrG1Verify" $ benchProgramCek ctx mkSchnorrG1VerifyPolicy

schnorrG2Verify :: EvaluationContext -> Benchmark
schnorrG2Verify ctx = bench "schnorrG2Verify" $ benchProgramCek ctx mkSchnorrG2VerifyPolicy

main :: IO ()
main = do
  evalCtx <- evaluate mkMostRecentEvalCtx
  defaultMain
    [ bgroup "hashAndAddG1" $ fmap (benchHashAndAddG1 evalCtx) [0, 10 .. 150]
    , bgroup "hashAndAddG2" $ fmap (benchHashAndAddG2 evalCtx) [0, 10 .. 150]
    , bgroup "uncompressAndAddG1" $ fmap (benchUncompressAndAddG1 evalCtx) [0, 10 .. 150]
    , bgroup "uncompressAndAddG2" $ fmap (benchUncompressAndAddG2 evalCtx) [0, 10 .. 150]
    , benchPairing evalCtx
    , benchGroth16Verify evalCtx
    , benchSimpleVerify evalCtx
    , benchVrf evalCtx
    , benchG1Verify evalCtx
    , benchG2Verify evalCtx
    , aggregateSigSingleKey evalCtx
    , aggregateSigMultiKey evalCtx
    , schnorrG1Verify evalCtx
    , schnorrG2Verify evalCtx
    ]
