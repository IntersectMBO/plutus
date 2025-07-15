-- editorconfig-checker-disable-file
{- | Print out the costs of various test scripts involving the BLS12_381
   primitives.  Most of these work on varying numbers of inputs so that we can
   get an idea of what we can do within the on-chain execution limits.
-}
module PlutusBenchmark.BLS12_381.RunTests (runTests)
where

import PlutusBenchmark.BLS12_381.Scripts
import PlutusBenchmark.Common

import PlutusTx.Prelude as Tx hiding ((*))

import Data.ByteString qualified as BS
import System.IO (Handle)
import Text.Printf (hPrintf)

import Prelude (IO, mapM_)

-- Run various tests and print information about their costs

printCosts_Pairing :: Handle -> IO ()
printCosts_Pairing h = do
    let emptyDST = toBuiltin BS.empty
        p1 = Tx.bls12_381_G1_hashToGroup (toBuiltin . BS.pack $ [0x23, 0x43, 0x56, 0xf2]) emptyDST
        p2 = Tx.bls12_381_G2_hashToGroup (toBuiltin . BS.pack $ [0x10, 0x00, 0xff, 0x88]) emptyDST
        q1 = Tx.bls12_381_G1_hashToGroup (toBuiltin . BS.pack $ [0x11, 0x22, 0x33, 0x44]) emptyDST
        q2 = Tx.bls12_381_G2_hashToGroup (toBuiltin . BS.pack $ [0xa0, 0xb1, 0xc2, 0xd3]) emptyDST
        script = mkPairingScript p1 p2 q1 q2
    printSizeStatistics h NoSize script

runTests :: Handle -> IO ()
runTests h = do

  hPrintf h "Apply pairing to two pairs of points in G1 x G2 and run finalVerify on the results\n\n"
  printHeader h
  printCosts_Pairing h
  hPrintf h "\n\n"

