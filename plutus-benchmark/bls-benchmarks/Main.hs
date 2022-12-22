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

import Prelude (Double, IO, Integral, String, fromIntegral, (*), (/))

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

{-# INLINABLE hashAndAdd #-}
hashAndAdd :: BuiltinByteString -> BuiltinByteString -> BuiltinBLS12_381_G1_Element
hashAndAdd s1 s2 =
    Tx.bls12_381_G1_add (Tx.bls12_381_G1_hashToCurve s1) (Tx.bls12_381_G1_hashToCurve s2)

{-# INLINABLE hashAndAddG1 #-}
hashAndAddG1 :: [BuiltinByteString] -> BuiltinBLS12_381_G1_Element
hashAndAddG1 [] = error ()
hashAndAddG1 (p:ps) =
    go ps (Tx.bls12_381_G1_hashToCurve p)
    where go [] acc     = acc
          go (q:qs) acc = go qs $ Tx.bls12_381_G1_add (Tx.bls12_381_G1_hashToCurve q) acc

mkScript :: [ByteString] -> UProg
mkScript l =
    let points = map toBuiltin l
    in Tx.getPlc $ $$(Tx.compile [|| hashAndAddG1 ||]) `Tx.applyCode` Tx.liftCode points

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
printStatistics :: Integer -> IO ()
printStatistics n = do
    let script = mkScript (listOfSizedByteStrings n 4)
        serialised = Flat.flat (toAnonDeBruijnProg script)
        size = BS.length serialised
        (cpu, mem) = evaluate script
    printf "  %3d %7d %8s %15d %8s %15d %8s \n"
           n
           size (percentTxt size max_tx_size)
           cpu  (percentTxt cpu  max_tx_ex_steps)
           mem  (percentTxt mem  max_tx_ex_mem)

-- | Check that the Haskell version succeeds on a list of inputs.
testHaskell :: Integer -> IO ()
testHaskell _n = return ()

main :: IO ()
main = do
  printf "    n     script size             CPU usage               Memory usage\n"
  printf "  ----------------------------------------------------------------------\n"
  mapM_ printStatistics [0, 10..150]
