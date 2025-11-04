{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Flat.Spec (test_flat) where

import Codec.Serialise (serialise)
import Data.ByteString qualified as BS
import Data.ByteString.Lazy qualified as BSL
import Data.Char (ord)
import Data.Word
import PlutusCore.Data (Data)
import PlutusCore.DeBruijn
import PlutusCore.Flat
import PlutusCore.Generators.QuickCheck.Builtin ()
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import UntypedPlutusCore ()
import UntypedPlutusCore.Core.Type

test_deBruijnIso :: TestTree
test_deBruijnIso = testProperty "deBruijnIso" $ \d ->
    d === fromFake (toFake d)

test_fakeIso :: TestTree
test_fakeIso = testProperty "fakeIso" $ \fnd ->
    fnd === toFake (fromFake fnd)

test_deBruijnTripping :: TestTree
test_deBruijnTripping = testProperty "debruijnTripping" $ \d ->
    Right d === unflat (flat @DeBruijn d)

test_fakeTripping :: TestTree
test_fakeTripping = testProperty "fakeTripping" $ \fnd ->
    Right fnd === unflat (flat @FakeNamedDeBruijn fnd)

test_binderDeBruijn :: TestTree
test_binderDeBruijn = testProperty "binderDeBruijn" $ \b ->
    -- binders should always decode as init binder
    Right initB === unflat (flat @(Binder DeBruijn) b)

test_binderFake :: TestTree
test_binderFake = testProperty "binderFake" $ \bf ->
    -- binders should always decode as init binder
    Right (toFake <$> initB) === unflat (flat @(Binder FakeNamedDeBruijn) bf)

{- Check that a bytestring is the canonical flat encoding of another bytestring.
A bytestring is encoded as sequence of chunks where each chunk is preceded by a
single byte giving its length and the end of the bytestring is marked by a
zero-length chunk.  The encoding is canonical if it consists of a (possibly
empty) sequence of 255-byte chunks followed by an optional smaller block
followed by an empty block.  See Note [Flat serialisation for strict and lazy
bytestrings].  See Appendix C of the Plutus Core specification for details of
the `flat` encoding, in particular Section C.2.5. -}
isCanonicalFlatEncodedByteString :: BS.ByteString -> Bool
isCanonicalFlatEncodedByteString bs =
  case BS.unpack bs of
    []     -> False   -- Should never happen.
    0x01:r -> go r    -- 0x01 is the tag for an encoded bytestring
                      --  (Plutus Core specification, Table C.2)
    _      -> False   -- Not the encoding of a bytestring.
  where
    go [] = False  -- We've fallen off the end, possibly due to having dropped too many bytes.
    go l@(w:ws) =  -- w is the purported size of the next chunk.
      if w == 0xFF
      then go (drop 255 ws)   -- Throw away any initial 255-byte chunks.
      else l == end || drop (fromIntegral w) ws == end
      -- Either we've arrived exactly at the end or we have a single short chunk before the end.
      where end = [0x00, 0x01] -- An empty chunk followed by a padding byte.

test_canonicalEncoding :: forall a . (Arbitrary a, Flat a, Show a) => String -> Int -> TestTree
test_canonicalEncoding s n =
  testProperty s $
  withMaxSuccess n $
  forAll (arbitrary @a) (isCanonicalFlatEncodedByteString . flat @a)

-- Data objects are encoded by first being converted to a bytestring using CBOR.
-- This is the case that we're really interested in, since we get a lazy
-- bytestring from CBOR and it has to converted into a strict one to ensure that
-- the encoding's canonical.
test_canonicalData :: TestTree
test_canonicalData =
  test_canonicalEncoding @Data "flat encodes Data canonically" 5000

-- We may as well check that it does the right thing for strict bytestrings
-- while we're here.
test_canonicalByteString :: TestTree
test_canonicalByteString =
  test_canonicalEncoding @BS.ByteString "flat encodes ByteStrings canonically" 1000

{- Some tests that non-canonically encoded bytestrings decode correctly to strict
bytestrings.  One strategy is to encode lazy bytestrings and decode the results
to get strict bytestrings and then check that the result is the same as
converting the original input into a strict bytestring, and we do this with
arbitrary lazy bytestrings and also ones obtained by CBOR-serialising `Data`
objects. However this will only test what we want when the lazy bytestring is
encoded non-canonically, which in fact happens quite rarely. To make sure that
we really do test some non-canonical inputs there are a few handwritten examples
as well. -}
test_nonCanonicalByteStringDecoding :: TestTree
test_nonCanonicalByteStringDecoding =
  let target = "This is a test." :: BS.ByteString

      ch :: Char -> Word8
      ch = fromIntegral . ord

      input1 = BS.pack [ 0x01  -- 0x01 is the tag for an encoded bytestring.
                       , 0x01, ch 'T'
                       , 0x01, ch 'h'
                       , 0x01, ch 'i'
                       , 0x01, ch 's'
                       , 0x01, ch ' '
                       , 0x01, ch 'i'
                       , 0x01, ch 's'
                       , 0x01, ch ' '
                       , 0x01, ch 'a'
                       , 0x01, ch ' '
                       , 0x01, ch 't'
                       , 0x01, ch 'e'
                       , 0x01, ch 's'
                       , 0x01, ch 't'
                       , 0x01, ch '.'
                       , 0x00
                       , 0x01 ]

      input2 = BS.pack [ 0x01
                       , 0x03, ch 'T', ch 'h', ch 'i'
                       , 0x03, ch 's', ch ' ', ch 'i'
                       , 0x03, ch 's', ch ' ', ch 'a'
                       , 0x03, ch ' ', ch 't', ch 'e'
                       , 0x03, ch 's', ch 't', ch '.'
                       , 0x00
                       , 0x01 ]

      input3 = BS.pack [ 0x01
                       , 0x01, ch 'T'
                       , 0x02, ch 'h', ch 'i'
                       , 0x03, ch 's', ch ' ', ch 'i'
                       , 0x04, ch 's', ch ' ', ch 'a', ch ' '
                       , 0x05, ch 't', ch 'e', ch 's', ch 't', ch '.'
                       , 0x00
                       , 0x01 ]

      input4 = BS.pack [ 0x01
                       , 0x05, ch 'T', ch 'h', ch 'i', ch 's', ch ' '
                       , 0x05, ch 'i', ch 's', ch ' ', ch 'a', ch ' '
                       , 0x05, ch 't', ch 'e', ch 's', ch 't', ch '.'
                       , 0x00
                       , 0x01 ]

      input5 = BS.pack [ 0x01
                       , 0x05, ch 'T', ch 'h', ch 'i', ch 's', ch ' '
                       , 0x04, ch 'i', ch 's', ch ' ', ch 'a'
                       , 0x03, ch ' ', ch 't', ch 'e'
                       , 0x02, ch 's', ch 't'
                       , 0x01, ch '.'
                       , 0x00
                       , 0x01 ]

      input6 = BS.pack [ 0x01
                       , 0x01, ch 'T'
                       , 0x0e, ch 'h', ch 'i', ch 's', ch ' ', ch 'i', ch 's', ch ' '
                       , ch 'a', ch ' ', ch 't', ch 'e', ch 's', ch 't', ch '.'
                       , 0x00
                       , 0x01 ]

      input7 = BS.pack [ 0x01
                       , 0x01, ch 'T'
                       , 0x0d, ch 'h', ch 'i', ch 's', ch ' ', ch 'i', ch 's', ch ' '
                       , ch 'a', ch ' ', ch 't', ch 'e', ch 's', ch 't'
                       , 0x01, ch '.'
                       , 0x00
                       , 0x01 ]

      input8 = BS.pack [ 0x01
                       , 0x03, ch 'T', ch 'h', ch 'i'
                       , 0x01, ch 's'
                       , 0x05, ch ' ', ch 'i', ch 's', ch ' ', ch 'a'
                       , 0x02, ch ' ', ch 't'
                       , 0x04, ch 'e', ch 's', ch 't', ch '.'
                       , 0x00
                       , 0x01 ]

      mkTest input =
        assertBool "Input failed to decode successfully" $
        (Right target == unflat input)

  in testGroup "Non-canonical bytestring encodings decode succesfully"
     [ testProperty "Data via lazy bytestrings" $
       withMaxSuccess 5000 $
       forAll (arbitrary @Data) (\d -> Right d === unflat (flat $ (serialise d :: BSL.ByteString)))
     , testProperty "Arbitrary lazy bytestrings" $
       withMaxSuccess 10000 $
       forAll (arbitrary @BSL.ByteString) (\bs -> Right (BSL.toStrict bs) === unflat (flat bs) )
     , testCase "Explicit input 1" $ mkTest input1
     , testCase "Explicit input 2" $ mkTest input2
     , testCase "Explicit input 3" $ mkTest input3
     , testCase "Explicit input 4" $ mkTest input4
     , testCase "Explicit input 5" $ mkTest input5
     , testCase "Explicit input 6" $ mkTest input6
     , testCase "Explicit input 7" $ mkTest input7
     , testCase "Explicit input 8" $ mkTest input8
     ]

test_flat :: TestTree
test_flat = testGroup "FlatProp"
    [ test_deBruijnIso
    , test_fakeIso
    , test_deBruijnTripping
    , test_fakeTripping
    , test_binderDeBruijn
    , test_binderFake
    , test_canonicalData
    , test_canonicalByteString
    , test_nonCanonicalByteStringDecoding
    ]

-- Helpers

initB :: Binder DeBruijn
initB = Binder $ DeBruijn deBruijnInitIndex

-- orphans for QuickCheck generation
deriving via Word64 instance Arbitrary DeBruijn
instance Arbitrary FakeNamedDeBruijn where
    arbitrary= toFake <$> arbitrary -- via debruijn
deriving newtype instance Arbitrary (Binder DeBruijn)
deriving newtype instance Arbitrary (Binder FakeNamedDeBruijn)
