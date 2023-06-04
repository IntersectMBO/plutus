-- editorconfig-checker-disable-file
{-# LANGUAGE LambdaCase #-}

{- | Print out the costs of various test scripts involving the BLS12_381
   primitives.  Most of these work on varying numbers of inputs so that we can
   get an idea of what we can do within the on-chain execution limits.
-}
module PlutusBenchmark.BLS12_381.RunTests (runTests)

where

import PlutusBenchmark.BLS12_381.Common
import PlutusBenchmark.ProtocolParameters as PP

import PlutusCore.Evaluation.Machine.ExBudget (ExBudget (exBudgetCPU, exBudgetMemory))
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as PLC
import PlutusCore.Evaluation.Machine.ExMemory (ExCPU (..), ExMemory (..))
import PlutusTx.Prelude as Tx hiding (sort, (*))
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as Cek

import Data.ByteString qualified as BS
import Data.SatInt (fromSatInt)
import Flat qualified
import System.IO (Handle, stdout)
import Text.Printf (hPrintf, printf)

import Prelude (Double, IO, Integral, String, fromIntegral, mapM_, show, (*), (/))

-------------------------------- Printing --------------------------------

data TestSize =
    NoSize
  | TestSize Integer

stringOfTestSize :: TestSize -> String
stringOfTestSize =
    \case
     NoSize     -> "-"
     TestSize n -> show n

-- Printing utilities
percentage :: (Integral a, Integral b) => a -> b -> Double
percentage a b =
    let a' = fromIntegral a :: Double
        b' = fromIntegral b :: Double
    in (a'* 100) / b'

percentTxt :: (Integral a, Integral b) => a -> b -> String
percentTxt a b = printf "(%.1f%%)" (percentage a b)

-- | Evaluate a script and return the CPU and memory costs (according to the cost model)
evaluate :: UProg -> (Integer, Integer)
evaluate (UPLC.Program _ _ prog) =
    case Cek.runCekDeBruijn PLC.defaultCekParameters Cek.tallying Cek.noEmitter prog of
      (_res, Cek.TallyingSt _ budget, _logs) ->
          let ExCPU cpu = exBudgetCPU budget
              ExMemory mem = exBudgetMemory budget
          in (fromSatInt cpu, fromSatInt mem)

-- | Evaluate a script and print out the serialised size and the CPU and memory
-- usage, both as absolute values and percentages of the maxima specified in the
-- protocol parameters.
printStatistics :: Handle -> TestSize -> UProg -> IO ()
printStatistics h n script = do
    let serialised = Flat.flat (UPLC.UnrestrictedProgram $ toAnonDeBruijnProg script)
        size = BS.length serialised
        (cpu, mem) = evaluate script
    hPrintf h "  %3s %7d %8s %15d %8s %15d %8s \n"
           (stringOfTestSize n)
           size (percentTxt size PP.max_tx_size)
           cpu  (percentTxt cpu  PP.max_tx_ex_steps)
           mem  (percentTxt mem  PP.max_tx_ex_mem)

------------------------------- Examples ---------------------------------

printCosts_HashAndAddG1 :: Handle -> Integer -> IO ()
printCosts_HashAndAddG1 h n =
    let script = mkHashAndAddG1Script (listOfSizedByteStrings n 4)
    in printStatistics h (TestSize n) script


printCosts_HashAndAddG2 :: Handle -> Integer -> IO ()
printCosts_HashAndAddG2 h n =
    let script = mkHashAndAddG2Script (listOfSizedByteStrings n 4)
    in printStatistics h (TestSize n) script


printCosts_UncompressAndAddG1 :: Handle -> Integer -> IO ()
printCosts_UncompressAndAddG1 h n =
    let script = mkUncompressAndAddG1Script (listOfSizedByteStrings n 4)
    in printStatistics h (TestSize n) script

printCosts_UncompressAndAddG2 :: Handle -> Integer -> IO ()
printCosts_UncompressAndAddG2 h n =
    let script = mkUncompressAndAddG2Script (listOfSizedByteStrings n 4)
    in printStatistics h (TestSize n) script

printCosts_Pairing :: Handle -> IO ()
printCosts_Pairing h = do
    let emptyDST = toBuiltin BS.empty
        p1 = Tx.bls12_381_G1_hashToGroup (toBuiltin . BS.pack $ [0x23, 0x43, 0x56, 0xf2]) emptyDST
        p2 = Tx.bls12_381_G2_hashToGroup (toBuiltin . BS.pack $ [0x10, 0x00, 0xff, 0x88]) emptyDST
        q1 = Tx.bls12_381_G1_hashToGroup (toBuiltin . BS.pack $ [0x11, 0x22, 0x33, 0x44]) emptyDST
        q2 = Tx.bls12_381_G2_hashToGroup (toBuiltin . BS.pack $ [0xa0, 0xb1, 0xc2, 0xd3]) emptyDST
        script = mkPairingScript p1 p2 q1 q2
    printStatistics h NoSize script

printCosts_Groth16Verify :: Handle -> IO ()
printCosts_Groth16Verify h = do
  let script = mkGroth16VerifyScript
  printStatistics h NoSize script

printHeader :: Handle -> IO ()
printHeader h = do
  hPrintf h "    n     script size             CPU usage               Memory usage\n"
  hPrintf h "  ----------------------------------------------------------------------\n"

runTests :: Handle -> IO ()
runTests h = do
  let h = stdout

  hPrintf h "Hash n bytestrings onto G1 and add points\n\n"
  printHeader h
  mapM_ (printCosts_HashAndAddG1 h) [0, 10..150]
  hPrintf h "\n\n"

  hPrintf h "Hash n bytestrings onto G2 and add points\n\n"
  printHeader h
  mapM_ (printCosts_HashAndAddG2 h) [0, 10..150]
  hPrintf h "\n\n"

  hPrintf h "Uncompress n G1 points and add the results\n\n"
  printHeader h
  mapM_ (printCosts_UncompressAndAddG1 h) [0, 10..150]
  hPrintf h "\n\n"

  hPrintf h "Uncompress n G2 points and add the results\n\n"
  printHeader h
  mapM_ (printCosts_UncompressAndAddG2 h) [0, 10..150]
  printf "\n\n"

  hPrintf h "Apply pairing to two pairs of points in G1 x G2 and run finalVerify on the results\n\n"
  printHeader h
  printCosts_Pairing h
  hPrintf h "\n\n"

  hPrintf h "Groth16 verification example\n\n"
  printHeader h
  printCosts_Groth16Verify h
  hPrintf h "\n"

  if checkGroth16Verify_Haskell
  then hPrintf h "Groth16Verify succeeded\n"
  else hPrintf h "Groth16Verify failed\n"

