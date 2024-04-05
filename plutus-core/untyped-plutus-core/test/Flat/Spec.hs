{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Flat.Spec (test_flat) where

import Data.ByteString qualified as BS
import Data.Word
import Flat
import PlutusCore.Data (Data)
import PlutusCore.DeBruijn
import PlutusCore.Generators.QuickCheck.Builtin ()
import Test.Tasty
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
bytestrings]. -}
isCanonicalFlatEncodedByteString :: BS.ByteString -> Bool
isCanonicalFlatEncodedByteString bs =
  case BS.unpack bs of
    []     -> False   -- Should never happen.
    0x01:r -> go r    -- 0x01 is the tag for an encoded bytestring.
    _      -> False   -- Not the encoding of a bytestring.
  where
    go [] = False  -- We've fallen off the end, possibly due to having dropped too many bytes.
    go l@(w:ws) =  -- w is the purported size of chunk.
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
  test_canonicalEncoding @Data "flat encodes Data canonically" 10000

-- We may as well check that it does the right thing for strict bytestrings
-- while we're here.
test_canonicalByteString :: TestTree
test_canonicalByteString =
  test_canonicalEncoding @BS.ByteString "flat encodes ByteStrings canonically" 1000

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
