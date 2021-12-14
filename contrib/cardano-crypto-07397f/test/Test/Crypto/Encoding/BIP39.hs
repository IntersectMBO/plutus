{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

module Test.Crypto.Encoding.BIP39
    ( tests
    ) where

import Foundation
import Foundation.Check
import Basement.Nat
import Basement.Types.OffsetSize (Offset(..))

import Data.ByteString (ByteString)
import qualified Data.ByteString as BS

import Crypto.Encoding.BIP39
import Crypto.Encoding.BIP39.English (english)

import Cardano.Internal.Compat (fromRight)

tests :: Test
tests = Group "BIP39"
    [ testsP @96  @9  @3 Proxy
    , testsP @128 @12 @4 Proxy
    , testsP @160 @15 @5 Proxy
    , testsP @192 @18 @6 Proxy
    , testsP @224 @21 @7 Proxy
    , testsP @256 @24 @8 Proxy
    , testsVector
    ]

testsP :: forall ent mw csz . (Arbitrary (Entropy ent), ConsistentEntropy ent mw csz)
       => Proxy ent
       -> Test
testsP _ = Group (show (natVal (Proxy @ent)))
    [ Property "wordsToEntropy . entropyToWords == id" $ \(e :: Entropy ent) ->
        (fromRight undefined . wordsToEntropy @ent) (entropyToWords e) === e
    ]

testsVector :: Test
testsVector = Group "Test Vector" $ runTest <$> testVectors

data TestVector = TestVector
    { testVectorInput  :: ByteString
    , testVectorWords  :: String
    , testVectorWIndex :: [Offset String]
    , testVectorSeed   :: Seed
    }

runTest :: TestVector -> Test
runTest tv =
    case BS.length (testVectorInput tv) * 8 of
        96  -> go (Proxy @96)
        128 -> go (Proxy @128)
        160 -> go (Proxy @160)
        192 -> go (Proxy @192)
        224 -> go (Proxy @224)
        256 -> go (Proxy @256)
        _   -> error "invalid size"
  where
    testVectorWIndex' = fmap wordIndex . testVectorWIndex

    go :: forall n csz mw . ConsistentEntropy n mw csz
       => Proxy n -> Test
    go proxyN = CheckPlan ("test " <> show (natVal proxyN)) $
        case toEntropy @n (testVectorInput tv) of
            Left err -> error $ show err
            Right e -> do
                let w = entropyToWords e
                    e' = fromRight undefined $ wordsToEntropy @n w
                    seed = sentenceToSeed w english "TREZOR"
                    words = mnemonicSentenceToString @mw english w
                validate "phrases are equal" (words === testVectorWords tv)
                validate "words equal" (toList w === testVectorWIndex' tv)
                validate "seed equal" (seed === testVectorSeed tv)
                validate "entropy equal" (e === e')

testVectors :: [TestVector]
testVectors =
    [ TestVector
        "\x7f\x7f\x7f\x7f\x7f\x7f\x7f\x7f\x7f\x7f\x7f\x7f\x7f\x7f\x7f\x7f"
        "legal winner thank year wave sausage worth useful legal winner thank yellow"
        [1019,2015,1790,2039,1983,1533,2031,1919,1019,2015,1790,2040]
        "\x2e\x89\x05\x81\x9b\x87\x23\xfe\x2c\x1d\x16\x18\x60\xe5\xee\x18\x30\x31\x8d\xbf\x49\xa8\x3b\xd4\x51\xcf\xb8\x44\x0c\x28\xbd\x6f\xa4\x57\xfe\x12\x96\x10\x65\x59\xa3\xc8\x09\x37\xa1\xc1\x06\x9b\xe3\xa3\xa5\xbd\x38\x1e\xe6\x26\x0e\x8d\x97\x39\xfc\xe1\xf6\x07"
    , TestVector
        "\x80\x80\x80\x80\x80\x80\x80\x80\x80\x80\x80\x80\x80\x80\x80\x80"
        "letter advice cage absurd amount doctor acoustic avoid letter advice cage above"
        [1028,32,257,8,64,514,16,128,1028,32,257,4]
        "\xd7\x1d\xe8\x56\xf8\x1a\x8a\xcc\x65\xe6\xfc\x85\x1a\x38\xd4\xd7\xec\x21\x6f\xd0\x79\x6d\x0a\x68\x27\xa3\xad\x6e\xd5\x51\x1a\x30\xfa\x28\x0f\x12\xeb\x2e\x47\xed\x2a\xc0\x3b\x5c\x46\x2a\x03\x58\xd1\x8d\x69\xfe\x4f\x98\x5e\xc8\x17\x78\xc1\xb3\x70\xb6\x52\xa8"
    , TestVector
        "\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff"
        "zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo wrong"
        [2047,2047,2047,2047,2047,2047,2047,2047,2047,2047,2047,2037]
        "\xac\x27\x49\x54\x80\x22\x52\x22\x07\x9d\x7b\xe1\x81\x58\x37\x51\xe8\x6f\x57\x10\x27\xb0\x49\x7b\x5b\x5d\x11\x21\x8e\x0a\x8a\x13\x33\x25\x72\x91\x7f\x0f\x8e\x5a\x58\x96\x20\xc6\xf1\x5b\x11\xc6\x1d\xee\x32\x76\x51\xa1\x4c\x34\xe1\x82\x31\x05\x2e\x48\xc0\x69"
    , TestVector
        "\x7f\x7f\x7f\x7f\x7f\x7f\x7f\x7f\x7f\x7f\x7f\x7f\x7f\x7f\x7f\x7f\x7f\x7f\x7f\x7f\x7f\x7f\x7f\x7f"
        "legal winner thank year wave sausage worth useful legal winner thank year wave sausage worth useful legal will"
        [1019,2015,1790,2039,1983,1533,2031,1919,1019,2015,1790,2039,1983,1533,2031,1919,1019,2009]
        "\xf2\xb9\x45\x08\x73\x2b\xcb\xac\xbc\xc0\x20\xfa\xef\xec\xfc\x89\xfe\xaf\xa6\x64\x9a\x54\x91\xb8\xc9\x52\xce\xde\x49\x6c\x21\x4a\x0c\x7b\x3c\x39\x2d\x16\x87\x48\xf2\xd4\xa6\x12\xba\xda\x07\x53\xb5\x2a\x1c\x7a\xc5\x3c\x1e\x93\xab\xd5\xc6\x32\x0b\x9e\x95\xdd"
    , TestVector
        "\xf5\x85\xc1\x1a\xec\x52\x0d\xb5\x7d\xd3\x53\xc6\x95\x54\xb2\x1a\x89\xb2\x0f\xb0\x65\x09\x66\xfa\x0a\x9d\x6f\x74\xfd\x98\x9d\x8f"
        "void come effort suffer camp survey warrior heavy shoot primary clutch crush open amazing screen patrol group space point ten exist slush involve unfold"
        [1964,368,565,1733,262,1749,1978,851,1588,1365,356,424,1241,62,1548,1289,823,1666,1338,1783,638,1634,945,1897]
        "\x01\xf5\xbc\xed\x59\xde\xc4\x8e\x36\x2f\x2c\x45\xb5\xde\x68\xb9\xfd\x6c\x92\xc6\x63\x4f\x44\xd6\xd4\x0a\xab\x69\x05\x65\x06\xf0\xe3\x55\x24\xa5\x18\x03\x4d\xdc\x11\x92\xe1\xda\xcd\x32\xc1\xed\x3e\xaa\x3c\x3b\x13\x1c\x88\xed\x8e\x7e\x54\xc4\x9a\x5d\x09\x98"
    ]
