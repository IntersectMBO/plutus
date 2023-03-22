-- editorconfig-checker-disable-file
{- | Plutus benchmarks measuring actual execution times of some BSL12-381
   operations, mainly intended to give us an idea of what we can do within the
   on-chain execution limits. -}
module Main where

import Criterion.Main

import PlutusBenchmark.BLS12_381.Common
import PlutusBenchmark.Common (benchTermCek)
import PlutusTx.Prelude qualified as Tx
import UntypedPlutusCore qualified as UPLC

benchProgCek :: UProg -> Benchmarkable
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
          let p1 = Tx.bls12_381_G1_hashToGroup $ Tx.toBuiltin b1
              p2 = Tx.bls12_381_G2_hashToGroup $ Tx.toBuiltin b2
              q1 = Tx.bls12_381_G1_hashToGroup $ Tx.toBuiltin b3
              q2 = Tx.bls12_381_G2_hashToGroup $ Tx.toBuiltin b4
              prog = mkPairingScript p1 p2 q1 q2
          in bench "pairing" $ benchProgCek prog
      _ -> error "Unexpected list returned by listOfSizedByteStrings"

benchGroth16Verify :: Benchmark
benchGroth16Verify = bench "groth16Verify" $ benchProgCek mkGroth16VerifyScript

main :: IO ()
main = do
  defaultMain [
          bgroup "hashAndAddG1" $ fmap benchHashAndAddG1 [0, 10..150]
        , bgroup "hashAndAddG2" $ fmap benchHashAndAddG2 [0, 10..150]
        , bgroup "uncompressAndAddG1" $ fmap benchUncompressAndAddG1 [0, 10..150]
        , bgroup "uncompressAndAddG2" $ fmap benchUncompressAndAddG2 [0, 10..150]
        , benchPairing
        , benchGroth16Verify
       ]
