{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import PlutusCore.Crypto.Hash qualified as Hash

import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Base16 qualified as Base16
import Data.ByteString.Lazy qualified as LBS
import Data.Word (Word8)
import Test.Tasty
import Test.Tasty.Golden (goldenVsString)

hashImpls :: [(String, ByteString -> ByteString)]
hashImpls =
  [ ("sha2_256", Hash.sha2_256)
  , ("sha3_256", Hash.sha3_256)
  , ("blake2b_224", Hash.blake2b_224)
  , ("blake2b_256", Hash.blake2b_256)
  , ("keccak_256", Hash.keccak_256)
  , ("ripemd_160", Hash.ripemd_160)
  ]

inputs :: [(String, ByteString)]
inputs =
  [ ("empty", BS.empty)
  , ("abc", "abc")
  , ("fox", "The quick brown fox jumps over the lazy dog")
  , ("byte00", BS.singleton 0x00)
  , ("byteff", BS.singleton 0xff)
  , ("allbytes", BS.pack [0 .. 255])
  , ("pseudorandom333", BS.pack [fromIntegral (i * 7 + 3) :: Word8 | i <- [0 .. 332 :: Int]])
  ]
    ++ [ ("len" ++ show n, BS.replicate n 0x61)
       | n <- [55, 56, 63, 64, 65, 127, 128, 129, 135, 136, 137, 1000]
       ]

main :: IO ()
main =
  defaultMain $
    testGroup
      "cryptographic hash goldens (with-crypto vs C-free parity)"
      [ testGroup
          hname
          [ goldenVsString
              iname
              ("test-crypto-hash-parity/golden/" ++ hname ++ "-" ++ iname ++ ".golden")
              (pure (LBS.fromStrict (Base16.encode (impl input))))
          | (iname, input) <- inputs
          ]
      | (hname, impl) <- hashImpls
      ]
