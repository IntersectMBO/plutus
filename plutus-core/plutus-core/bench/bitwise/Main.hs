-- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Benches.Binary qualified as Binary
import Benches.BitRead qualified as BitRead
import Benches.BitWrite qualified as BitWrite
import Benches.Complement qualified as Complement
import Benches.Convert qualified as Convert
import Benches.CountLeadingZeroes qualified as CountLeadingZeroes
import Benches.Popcount qualified as Popcount
import Benches.Rotate qualified as Rotate
import Benches.Shift qualified as Shift
import GHC.IO.Encoding (setLocaleEncoding, utf8)
import Test.Tasty (testGroup)
import Test.Tasty.Bench (defaultMain)

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
    testGroup "Bit rotate" [
      Rotate.benches
      ],
    testGroup "Conversions" [
      Convert.benchesBSToI
      ]
    ]
