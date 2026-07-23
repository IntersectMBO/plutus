{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Main where

import PlutusCore.Default
import PlutusCore.Flat qualified as PlutusFlat
import PlutusCore.MkPlc
import PlutusCore.Version
import PlutusLedgerApi.Common.Versions
import PlutusLedgerApi.V1
import UntypedPlutusCore as UPLC

import Control.DeepSeq (force)
import Control.Exception
import Criterion
import Criterion.Main
import Data.ByteString as BS
import Data.Functor (void)
import Data.Vector.Strict qualified as V
import Flat

unsafeUnflat :: forall a. Flat a => BS.ByteString -> a
unsafeUnflat x =
  case unflat x of
    Left _ -> errorWithoutStackTrace "Can't unflatten"
    Right (y :: a) -> y

-- Make an integer with n decimal digits using the seed k.
mkInteger :: Integer -> Integer -> Integer
mkInteger n k =
  if n <= 1
    then k `mod` 10
    else 10 * mkInteger (n - 1) (k + 1) + (k * k + 7 * k + 1) `mod` 10

-- Make a semi-random bytestring of length n using the seed k.  This will
-- repeat after a while, but that's not too important.
mkByteString :: Integer -> Integer -> ByteString
mkByteString k lim = BS.unfoldr f k
  where
    f n =
      if n < lim
        then Just (fromIntegral $ n * n + 7 * n + k, n + 1)
        else Nothing

-- Given a list of (size, object) pairs, create a benchmark for each
-- object, labelled with its size.
mkBM :: DefaultUni `Contains` a => (Integer, a) -> Benchmark
mkBM (sz, a) =
  let !(script :: SerialisedScript) = force $ serialiseUPLC (mkProg a)
   in bench (show sz) $
        whnf (either throw id . void . deserialiseScript futurePV) script

mkProg
  :: DefaultUni `Contains` a
  => a
  -> UPLC.Program DeBruijn DefaultUni DefaultFun ()
mkProg a = UPLC.Program () plcVersion100 $ mkConstant () a

-- Decode an unpadded Integer directly, so this benchmark isolates the Flat
-- integer decoder from UPLC term decoding and validation.
unsafeUnflatRawInteger :: BS.ByteString -> Integer
unsafeUnflatRawInteger encoded =
  case PlutusFlat.unflatRaw encoded of
    Left err -> throw err
    Right value -> value

-- A sparse input establishes the cost of reading the bytes and constructing
-- the final Integer while doing only one nonzero shift.
sparseIntegerEncoding :: Int -> BS.ByteString
sparseIntegerEncoding chunks =
  BS.replicate (chunks - 1) 0x80 <> BS.singleton 0x02

-- Every payload chunk is nonzero. The first payload digit is even so ZigZag
-- decodes the result as a positive Integer; the last byte terminates the value.
denseIntegerEncoding :: Int -> BS.ByteString
denseIntegerEncoding chunks
  | chunks == 1 = BS.singleton 0x02
  | otherwise =
      BS.singleton 0x82
        <> BS.replicate (chunks - 2) 0x81
        <> BS.singleton 0x01

integerEncodingSizes :: [Int]
integerEncodingSizes = [128, 256, 512, 1024, 2048, 4096, 8192, 16384]

mkIntegerMagnitudeBMs :: String -> (Int -> BS.ByteString) -> Benchmark
mkIntegerMagnitudeBMs label mkEncoding =
  bgroup label $
    fmap
      ( \chunks ->
          env (pure $ force $ mkEncoding chunks) $ \ ~encoded ->
            bench (show chunks) $ nf unsafeUnflatRawInteger encoded
      )
      integerEncodingSizes

main :: IO ()
main =
  let lengths :: [Integer] = fmap (100 *) [1 .. 20]

      -- For each element `n` of `lengths`, create a benchmark that measures the
      -- time required to deserialise a UPLC list containing `n` elements
      -- obtained by applying `mkInput` to [1..n]
      mkListBMs :: DefaultUni `Contains` a => (Integer -> a) -> [Benchmark]
      mkListBMs mkInput = fmap mkBM $ fmap (\n -> (n, fmap mkInput [1 .. n])) lengths

      -- For each element `n` of `lengths`, create a benchmark that measures the
      -- time required to deserialise a UPLC array containing `n` elements
      -- obtained by applying `mkInput` to [1..n]
      mkArrayBMs :: DefaultUni `Contains` a => (Integer -> a) -> [Benchmark]
      mkArrayBMs mkInput = fmap mkBM $ fmap (\n -> (n, fmap mkInput $ V.fromList [1 .. n])) lengths
   in defaultMain
        [ bgroup
            "single-integer/by-varint-bytes"
            [ mkIntegerMagnitudeBMs "dense-payload" denseIntegerEncoding
            , mkIntegerMagnitudeBMs "sparse-payload" sparseIntegerEncoding
            ]
        , bgroup
            "list"
            [ bgroup "bool" . mkListBMs $ \i -> i `mod` 2 == 0
            , bgroup
                "integer"
                [ bgroup "small" . mkListBMs $ mkInteger 5
                , bgroup "big" . mkListBMs $ mkInteger 100
                ]
            , bgroup
                "bytestring"
                [ bgroup "small" . mkListBMs $ mkByteString 16
                , bgroup "big" . mkListBMs $ mkByteString 1024
                ]
            ]
        , bgroup
            "array"
            [ bgroup "bool" . mkArrayBMs $ \i -> i `mod` 2 == 0
            , bgroup
                "integer"
                [ bgroup "small" . mkArrayBMs $ mkInteger 5
                , bgroup "big" . mkArrayBMs $ mkInteger 100
                ]
            , bgroup
                "bytestring"
                [ bgroup "small" . mkArrayBMs $ mkByteString 16
                , bgroup "big" . mkArrayBMs $ mkByteString 1024
                ]
            ]
        ]
