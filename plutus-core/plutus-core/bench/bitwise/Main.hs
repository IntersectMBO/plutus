-- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Benches.Binary qualified as Binary
import Benches.BitRead qualified as BitRead
import Benches.BitWrite qualified as BitWrite
import Benches.Complement qualified as Complement
import Benches.CountLeadingZeroes qualified as CountLeadingZeroes
import Benches.Homogenous qualified as Homogenous
import Benches.Popcount qualified as Popcount
import Benches.Shift qualified as Shift
import Data.Bits (complement, zeroBits, (.&.))
import Data.ByteString qualified as BS
import DataGen (mkUnaryArg, noCleanup, sizes)
import GHC.IO.Encoding (setLocaleEncoding, utf8)
import Implementations (rotateBS, rotateBSFast)
import Test.Tasty (testGroup, withResource)
import Test.Tasty.Bench (Benchmark, bcompare, bench, bgroup, defaultMain, nfIO)

main :: IO ()
main = do
  setLocaleEncoding utf8
  defaultMain [
    testGroup "Popcount" [
      Popcount.benches,
      Popcount.cBenches
      ],
    testGroup "Complement" [
      Complement.benches
      ],
    testGroup "Homogenous" [
      Homogenous.benches
      ],
    testGroup "Binary" [
      Binary.benches
      ],
    testGroup "Count leading zeroes" [
      CountLeadingZeroes.benches,
      CountLeadingZeroes.cBenches
      ],
    testGroup "Bit read" [
      BitRead.benches
      ],
    testGroup "Bit write" [
      BitWrite.benches
      ],
    testGroup "Bit shift" [
      Shift.benches
      ],
    bgroup rotateLabel . fmap (rotateVsPrescanBench rotateLabel) $ sizes,
    bgroup rotateLabel' . fmap (rotateFastVsSlow rotateLabel') $ sizes
    ]
  where
    rotateLabel :: String
    rotateLabel = "Slow rotate versus prescan"
    rotateLabel' :: String
    rotateLabel' = "Bitwise rotate versus block rotate"

-- Benchmarks

rotateFastVsSlow ::
  String ->
  Int ->
  Benchmark
rotateFastVsSlow mainLabel len =
  withResource (mkUnaryArg len) noCleanup $ \xs ->
    let rLabel = "rotate (bit-by-bit)"
        rLabel' = "rotate (block-optimized)"
        -- Next highest multiple of 8 of half our length, rounded down
        rotation = ((len `quot` 2) + 7) .&. negate 8
        testLabel = mainLabel <> ", length " <> show len <> ", rotation by " <> show rotation
        matchLabel = "$NF == \"" <> rLabel <> "\" && $(NF - 1) == \"" <> testLabel <> "\"" in
      bgroup testLabel [
        bench rLabel . nfIO $ rotateBS <$> xs <*> pure rotation,
        bcompare matchLabel . bench rLabel' . nfIO $ rotateBSFast <$> xs <*> pure rotation
        ]

rotateVsPrescanBench ::
  String ->
  Int ->
  Benchmark
rotateVsPrescanBench mainLabel len =
  withResource (mkUnaryArg len) noCleanup $ \xs ->
    let rLabel = "rotate (bit-by-bit)"
        pLabel = "prescan (naive)"
        rotation = len `quot` 2
        testLabel = mainLabel <> ", length " <> show len
        matchLabel = "$NF == \"" <> rLabel <> "\" && $(NF - 1) == \"" <> testLabel <> "\"" in
      bgroup testLabel [
        bench rLabel . nfIO $ rotateBS <$> xs <*> pure rotation,
        bcompare matchLabel . bench pLabel . nfIO $ (||) <$> (BS.all (== zeroBits) <$> xs) <*>
                                                             (BS.all (== complement zeroBits) <$> xs)
        ]

