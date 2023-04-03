-- editorconfig-checker-disable-file
{-# LANGUAGE NumericUnderscores #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

{- | Print out the costs of various test scripts involving the BLS12_381
   primitives.  Most of these work on varying numbers of inputs so that we can
   get an idea of what we can do within the on-chain execution limits.
-}
module Main (main)

where

import PlutusBenchmark.BLS12_381.Common

import PlutusCore.Evaluation.Machine.ExBudget (ExBudget (exBudgetCPU, exBudgetMemory))
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as PLC
import PlutusCore.Evaluation.Machine.ExMemory (ExCPU (..), ExMemory (..))
import PlutusTx.Prelude as Tx hiding (sort, (*))
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as Cek

import Data.ByteString qualified as BS
import Flat qualified
import Text.Printf (printf)

import Prelude (Double, IO, Integral, String, fromIntegral, mapM_, show, (*), (/))

-- Protocol parameters (November 2022)

-- | This is the "maximum transaction size".  We're just comparing the size of
-- the script with this, so our results may be a little optimistic if the
-- transaction includes other stuff (I'm not sure exactly what "maximum
-- transaction size" means).
max_tx_size :: Integer
max_tx_size = 16384

max_tx_ex_steps :: Integer
max_tx_ex_steps = 10_000_000_000

max_tx_ex_mem :: Integer
max_tx_ex_mem = 14_000_000

-------------------------------- Printing --------------------------------

-- Printing utilities
percentage :: (Integral a, Integral b) => a -> b -> Double
percentage a b =
    let a' = fromIntegral a :: Double
        b' = fromIntegral b :: Double
    in (a'/b' * 100)

percentTxt :: (Integral a, Integral b) => a -> b -> String
percentTxt a b = printf "(%.1f%%)" (percentage a b)

-- | Evaluate a script and return the CPU and memory costs (according to the cost model)
evaluate :: UProg -> (Integer, Integer)
evaluate (UPLC.Program _ _ prog) =
    case Cek.runCekDeBruijn PLC.defaultCekParameters Cek.tallying Cek.noEmitter prog of
      (_res, Cek.TallyingSt _ budget, _logs) ->
          let ExCPU cpu = exBudgetCPU budget
              ExMemory mem = exBudgetMemory budget
          in (fromIntegral cpu, fromIntegral mem)

-- | Evaluate a script and print out the serialised size and the CPU and memory
-- usage, both as absolute values and percentages of the maxima specified in the
-- protocol parameters.
printStatistics :: Integer -> UProg -> IO ()
printStatistics n script = do
    let serialised = Flat.flat (UPLC.UnrestrictedProgram $ toAnonDeBruijnProg script)
        size = BS.length serialised
        (cpu, mem) = evaluate script
    -- BS.writeFile "output" serialised
    -- printf "%s\n" $ show $ PP.prettyClassicDebug script
    printf "  %3s %7d %8s %15d %8s %15d %8s \n"
           (if n > 0 then show n else "-")
           size (percentTxt size max_tx_size)
           cpu  (percentTxt cpu  max_tx_ex_steps)
           mem  (percentTxt mem  max_tx_ex_mem)

------------------------------- Examples ---------------------------------

printCosts_HashAndAddG1 :: Integer -> IO ()
printCosts_HashAndAddG1 n =
    let script = mkHashAndAddG1Script (listOfSizedByteStrings n 4)
    in printStatistics n script


printCosts_HashAndAddG2 :: Integer -> IO ()
printCosts_HashAndAddG2 n =
    let script = mkHashAndAddG2Script (listOfSizedByteStrings n 4)
    in printStatistics n script


printCosts_UncompressAndAddG1 :: Integer -> IO ()
printCosts_UncompressAndAddG1 n =
    let script = mkUncompressAndAddG1Script (listOfSizedByteStrings n 4)
    in printStatistics n script

printCosts_UncompressAndAddG2 :: Integer -> IO ()
printCosts_UncompressAndAddG2 n =
    let script = mkUncompressAndAddG2Script (listOfSizedByteStrings n 4)
    in printStatistics n script

printCosts_Pairing :: IO ()
printCosts_Pairing = do
    let p1 = Tx.bls12_381_G1_hashToGroup $ toBuiltin $ BS.pack [0x23, 0x43, 0x56, 0xf2]
        p2 = Tx.bls12_381_G2_hashToGroup $ toBuiltin $ BS.pack [0x10, 0x00, 0xff, 0x88]
        q1 = Tx.bls12_381_G1_hashToGroup $ toBuiltin $ BS.pack [0x11, 0x22, 0x33, 0x44]
        q2 = Tx.bls12_381_G2_hashToGroup $ toBuiltin $ BS.pack [0xa0, 0xb1, 0xc2, 0xd3]
        script = mkPairingScript p1 p2 q1 q2
    printStatistics (-1) script

printCosts_Groth16Verify :: IO ()
printCosts_Groth16Verify = do
  let script = mkGroth16VerifyScript
  printStatistics (-1) script

printHeader :: IO ()
printHeader = do
  printf "    n     script size             CPU usage               Memory usage\n"
  printf "  ----------------------------------------------------------------------\n"

main :: IO ()
main = do

  printf "Hash n bytestrings onto G1 and add points\n\n"
  printHeader
  mapM_ printCosts_HashAndAddG1 [0, 10..150]
  printf "\n\n"

  printf "Hash n bytestrings onto G2 and add points\n\n"
  printHeader
  mapM_ printCosts_HashAndAddG2 [0, 10..150]
  printf "\n\n"

  printf "Uncompress n G1 points and add the results\n\n"
  printHeader
  mapM_ printCosts_UncompressAndAddG1 [0, 10..150]
  printf "\n\n"

  printf "Uncompress n G2 points and add the results\n\n"
  printHeader
  mapM_ printCosts_UncompressAndAddG2 [0, 10..150]
  printf "\n\n"

  printf "Apply pairing to two pairs of points in G1 x G2 and run finalVerify on the results\n\n"
  printHeader
  printCosts_Pairing
  printf "\n\n"

  printf "Groth16 verification example\n\n"
  printHeader
  printCosts_Groth16Verify
  printf "\n"

  if checkGroth16Verify_Haskell
  then printf "Groth16Verify succeeded\n"
  else printf "Groth16Verify failed\n"


