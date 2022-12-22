-- editorconfig-checker-disable-file
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE NumericUnderscores  #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE ViewPatterns        #-}

{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

{- | Check how many Ed25519 signature verifications we can perform within the
   limits specified in the protocol parameters.
-}

module Main (main)

where

import PlutusCore (DefaultFun, DefaultUni)
import PlutusCore.Evaluation.Machine.ExBudget (ExBudget (exBudgetCPU, exBudgetMemory))
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as PLC
import PlutusCore.Evaluation.Machine.ExMemory (ExCPU (..), ExMemory (..))
import PlutusCore.Pretty qualified as PP
import PlutusTx qualified as Tx
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as Cek

import PlutusTx.IsData (toData, unstableMakeIsData)
import PlutusTx.Prelude as Tx hiding (sort, (*))

import Cardano.Crypto.DSIGN.Class (ContextDSIGN, DSIGNAlgorithm, Signable, deriveVerKeyDSIGN, genKeyDSIGN,
                                   rawSerialiseSigDSIGN, rawSerialiseVerKeyDSIGN, signDSIGN)
import Cardano.Crypto.DSIGN.Ed25519 (Ed25519DSIGN)
import Cardano.Crypto.Seed (mkSeedFromBytes)

import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Hash qualified as Hash
import Flat qualified
import Hedgehog.Internal.Gen qualified as G
import Hedgehog.Internal.Range qualified as R
import System.IO.Unsafe (unsafePerformIO)
import Text.Printf (printf)

import Prelude (Double, IO, Integral, String, fromIntegral, show, (*), (/))

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


-------------------------------- PLC stuff--------------------------------

type UTerm   = UPLC.Term    UPLC.NamedDeBruijn DefaultUni DefaultFun ()
type UProg   = UPLC.Program UPLC.NamedDeBruijn DefaultUni DefaultFun ()
type UDBProg = UPLC.Program UPLC.DeBruijn      DefaultUni DefaultFun ()


compiledCodeToTerm
    :: Tx.CompiledCodeIn DefaultUni DefaultFun () a -> UTerm
compiledCodeToTerm (Tx.getPlc -> UPLC.Program _ _ body) = body

{- | Remove the textual names from a NamedDeBruijn program -}
toAnonDeBruijnProg :: UProg -> UDBProg
toAnonDeBruijnProg (UPLC.Program () ver body) =
    UPLC.Program () ver $ UPLC.termMapNames (\(UPLC.NamedDeBruijn _ ix) -> UPLC.DeBruijn ix) body

-- Create a list containing n bytestrings of length l.  This could be better.
listOfSizedByteStrings :: Integer -> Integer -> [ByteString]
listOfSizedByteStrings n l = unsafePerformIO . G.sample $
                             G.list (R.singleton $ fromIntegral n)
                                  (G.bytes (R.singleton $ fromIntegral l))

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
    let serialised = Flat.flat (toAnonDeBruijnProg script)
        size = BS.length serialised
        (cpu, mem) = evaluate script
    printf "  %3d %7d %8s %15d %8s %15d %8s \n"
           n
           size (percentTxt size max_tx_size)
           cpu  (percentTxt cpu  max_tx_ex_steps)
           mem  (percentTxt mem  max_tx_ex_mem)

------------------------------- Examples ---------------------------------

-- Adding points in G1

{-# INLINABLE hashAndAddG1 #-}
hashAndAddG1 :: [BuiltinByteString] -> BuiltinBLS12_381_G1_Element
hashAndAddG1 [] = error ()
hashAndAddG1 (p:ps) =
    go ps (Tx.bls12_381_G1_hashToCurve p)
    where go [] acc     = acc
          go (q:qs) acc = go qs $ Tx.bls12_381_G1_add (Tx.bls12_381_G1_hashToCurve q) acc

mkHashAndAddG1Script :: [ByteString] -> UProg
mkHashAndAddG1Script l =
    let points = map toBuiltin l
    in Tx.getPlc $ $$(Tx.compile [|| hashAndAddG1 ||]) `Tx.applyCode` Tx.liftCode points

testHashAndAddG1 :: Integer -> IO ()
testHashAndAddG1 n =
    let script = mkHashAndAddG1Script (listOfSizedByteStrings n 4)
    in printStatistics n script

-- Adding points in G2

{-# INLINABLE hashAndAddG2 #-}
hashAndAddG2 :: [BuiltinByteString] -> BuiltinBLS12_381_G2_Element
hashAndAddG2 [] = error ()
hashAndAddG2 (p:ps) =
    go ps (Tx.bls12_381_G2_hashToCurve p)
    where go [] acc     = acc
          go (q:qs) acc = go qs $ Tx.bls12_381_G2_add (Tx.bls12_381_G2_hashToCurve q) acc

mkHashAndAddG2Script :: [ByteString] -> UProg
mkHashAndAddG2Script l =
    let points = map toBuiltin l
    in Tx.getPlc $ $$(Tx.compile [|| hashAndAddG2 ||]) `Tx.applyCode` Tx.liftCode points

testHashAndAddG2 :: Integer -> IO ()
testHashAndAddG2 n =
    let script = mkHashAndAddG2Script (listOfSizedByteStrings n 4)
    in printStatistics n script

-- Pairing operations

{-# INLINABLE runPairingFunctions #-}
runPairingFunctions
    :: Tx.BuiltinBLS12_381_G1_Element
    -> Tx.BuiltinBLS12_381_G2_Element
    -> Tx.BuiltinBLS12_381_G1_Element
    -> Tx.BuiltinBLS12_381_G2_Element
    -> Bool
runPairingFunctions p1 p2 q1 q2 =
    let r1 = Tx.bls12_381_millerLoop p1 p2
        r2 = Tx.bls12_381_millerLoop q1 q2
    in Tx.bls12_381_finalVerify r1 r2

makePairingScript
    :: BuiltinBLS12_381_G1_Element
    -> BuiltinBLS12_381_G2_Element
    -> BuiltinBLS12_381_G1_Element
    -> BuiltinBLS12_381_G2_Element
    -> UProg
makePairingScript p1 p2 q1 q2 =
    Tx.getPlc $ $$(Tx.compile [|| runPairingFunctions ||])
          `Tx.applyCode` Tx.liftCode p1
          `Tx.applyCode` Tx.liftCode p2
          `Tx.applyCode` Tx.liftCode q1
          `Tx.applyCode` Tx.liftCode q2

testPairing :: IO ()
testPairing = do
    let p1 = Tx.bls12_381_G1_hashToCurve $ toBuiltin $ BS.pack [0x23, 0x43, 0x56, 0xf2]
        p2 = Tx.bls12_381_G2_hashToCurve $ toBuiltin $ BS.pack [0x10, 0x00, 0xff, 0x88]
        q1 = Tx.bls12_381_G1_hashToCurve $ toBuiltin $ BS.pack [0x11, 0x22, 0x33, 0x44]
        q2 = Tx.bls12_381_G2_hashToCurve $ toBuiltin $ BS.pack [0xa0, 0xb1, 0xc2, 0xd3]
        script = makePairingScript p1 p2 q1 q2
    printStatistics 1 script
--    printf $ show $ PP.prettyClassicDebug script

main :: IO ()
main = do
  printf "    n     script size             CPU usage               Memory usage\n"
  printf "  ----------------------------------------------------------------------\n"
  mapM_ testHashAndAddG2 [0, 10..150]
--  testPairing

