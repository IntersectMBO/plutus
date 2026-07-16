{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Flat.Spec (test_flat) where

import Codec.Serialise (serialise)
import Data.ByteString qualified as BS
import Data.ByteString.Lazy qualified as BSL
import Data.Char (ord)
import Data.Vector qualified as Vector
import Data.Word
import PlutusCore.Data (Data)
import PlutusCore.DeBruijn
import PlutusCore.Default
  ( DefaultBuiltinPattern (..)
  , DefaultFun (..)
  , DefaultUni (..)
  )
import PlutusCore.Flat
import PlutusCore.Flat.Bits (asBytes, bits)
import PlutusCore.FlatInstances (safeEncodeBits)
import PlutusCore.Generators.QuickCheck.Builtin ()
import PlutusCore.Name.Unique (Name (..), TyName (..), Unique (..))
import PlutusCore.Version (knownVersions, latestVersion, plcVersion110, plcVersion120)
import Test.Cardano.Base.QuickCheck qualified as BaseQC
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck hiding (Some, getSize)
import Universe (Some (..), ValueOf (..))
import UntypedPlutusCore.Core.Type

-- Also brings the Flat (Strict.Vector a) orphan instance into scope:
import UntypedPlutusCore
  ( UnrestrictedProgram (..)
  , decodeProgram
  , decodeTerm
  )

-- | An encode-only value for exercising reserved Flat tags through the real decoders.
data RawTag = RawTag Int Word8

instance Flat RawTag where
  encode (RawTag width tag) = safeEncodeBits width tag
  decode = fail "RawTag is encode-only"
  size (RawTag width _) n = width + n

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
    [] -> False -- Should never happen.
    0x01 : r -> go r -- 0x01 is the tag for an encoded bytestring
    --  (Plutus Core specification, Table C.2)
    _ -> False -- Not the encoding of a bytestring.
  where
    go [] = False -- We've fallen off the end, possibly due to having dropped too many bytes.
    go l@(w : ws) =
      -- w is the purported size of the next chunk.
      if w == 0xFF
        then go (drop 255 ws) -- Throw away any initial 255-byte chunks.
        else l == end || drop (fromIntegral w) ws == end
      where
        -- Either we've arrived exactly at the end or we have a single short chunk before the end.
        end = [0x00, 0x01] -- An empty chunk followed by a padding byte.

test_canonicalEncoding :: forall a. (Arbitrary a, Flat a, Show a) => String -> Int -> TestTree
test_canonicalEncoding s n =
  testProperty s $
    BaseQC.withNumTests n $
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

      input1 =
        BS.pack
          [ 0x01 -- 0x01 is the tag for an encoded bytestring.
          , 0x01
          , ch 'T'
          , 0x01
          , ch 'h'
          , 0x01
          , ch 'i'
          , 0x01
          , ch 's'
          , 0x01
          , ch ' '
          , 0x01
          , ch 'i'
          , 0x01
          , ch 's'
          , 0x01
          , ch ' '
          , 0x01
          , ch 'a'
          , 0x01
          , ch ' '
          , 0x01
          , ch 't'
          , 0x01
          , ch 'e'
          , 0x01
          , ch 's'
          , 0x01
          , ch 't'
          , 0x01
          , ch '.'
          , 0x00
          , 0x01
          ]

      input2 =
        BS.pack
          [ 0x01
          , 0x03
          , ch 'T'
          , ch 'h'
          , ch 'i'
          , 0x03
          , ch 's'
          , ch ' '
          , ch 'i'
          , 0x03
          , ch 's'
          , ch ' '
          , ch 'a'
          , 0x03
          , ch ' '
          , ch 't'
          , ch 'e'
          , 0x03
          , ch 's'
          , ch 't'
          , ch '.'
          , 0x00
          , 0x01
          ]

      input3 =
        BS.pack
          [ 0x01
          , 0x01
          , ch 'T'
          , 0x02
          , ch 'h'
          , ch 'i'
          , 0x03
          , ch 's'
          , ch ' '
          , ch 'i'
          , 0x04
          , ch 's'
          , ch ' '
          , ch 'a'
          , ch ' '
          , 0x05
          , ch 't'
          , ch 'e'
          , ch 's'
          , ch 't'
          , ch '.'
          , 0x00
          , 0x01
          ]

      input4 =
        BS.pack
          [ 0x01
          , 0x05
          , ch 'T'
          , ch 'h'
          , ch 'i'
          , ch 's'
          , ch ' '
          , 0x05
          , ch 'i'
          , ch 's'
          , ch ' '
          , ch 'a'
          , ch ' '
          , 0x05
          , ch 't'
          , ch 'e'
          , ch 's'
          , ch 't'
          , ch '.'
          , 0x00
          , 0x01
          ]

      input5 =
        BS.pack
          [ 0x01
          , 0x05
          , ch 'T'
          , ch 'h'
          , ch 'i'
          , ch 's'
          , ch ' '
          , 0x04
          , ch 'i'
          , ch 's'
          , ch ' '
          , ch 'a'
          , 0x03
          , ch ' '
          , ch 't'
          , ch 'e'
          , 0x02
          , ch 's'
          , ch 't'
          , 0x01
          , ch '.'
          , 0x00
          , 0x01
          ]

      input6 =
        BS.pack
          [ 0x01
          , 0x01
          , ch 'T'
          , 0x0e
          , ch 'h'
          , ch 'i'
          , ch 's'
          , ch ' '
          , ch 'i'
          , ch 's'
          , ch ' '
          , ch 'a'
          , ch ' '
          , ch 't'
          , ch 'e'
          , ch 's'
          , ch 't'
          , ch '.'
          , 0x00
          , 0x01
          ]

      input7 =
        BS.pack
          [ 0x01
          , 0x01
          , ch 'T'
          , 0x0d
          , ch 'h'
          , ch 'i'
          , ch 's'
          , ch ' '
          , ch 'i'
          , ch 's'
          , ch ' '
          , ch 'a'
          , ch ' '
          , ch 't'
          , ch 'e'
          , ch 's'
          , ch 't'
          , 0x01
          , ch '.'
          , 0x00
          , 0x01
          ]

      input8 =
        BS.pack
          [ 0x01
          , 0x03
          , ch 'T'
          , ch 'h'
          , ch 'i'
          , 0x01
          , ch 's'
          , 0x05
          , ch ' '
          , ch 'i'
          , ch 's'
          , ch ' '
          , ch 'a'
          , 0x02
          , ch ' '
          , ch 't'
          , 0x04
          , ch 'e'
          , ch 's'
          , ch 't'
          , ch '.'
          , 0x00
          , 0x01
          ]

      mkTest input =
        assertBool "Input failed to decode successfully" $
          (Right target == unflat input)
   in testGroup
        "Non-canonical bytestring encodings decode succesfully"
        [ testProperty "Data via lazy bytestrings" $
            BaseQC.withNumTests 5000 $ forAll (arbitrary @Data) \d ->
              Right d === unflat (flat (serialise d :: BSL.ByteString))
        , testProperty "Arbitrary lazy bytestrings" $
            BaseQC.withNumTests 10000 $
              forAll (arbitrary @BSL.ByteString) \bs ->
                Right (BSL.toStrict bs) === unflat (flat bs)
        , testCase "Explicit input 1" $ mkTest input1
        , testCase "Explicit input 2" $ mkTest input2
        , testCase "Explicit input 3" $ mkTest input3
        , testCase "Explicit input 4" $ mkTest input4
        , testCase "Explicit input 5" $ mkTest input5
        , testCase "Explicit input 6" $ mkTest input6
        , testCase "Explicit input 7" $ mkTest input7
        , testCase "Explicit input 8" $ mkTest input8
        ]

{-| Stable byte encoding tests for Binder types.
These pin the exact byte representation to detect encoding changes. -}
test_binderStaticEncoding :: TestTree
test_binderStaticEncoding =
  testGroup
    "Binder stable encoding"
    [ testCase "Binder DeBruijn encodes as empty (zero-cost)" $
        flatBytes (Binder (DeBruijn deBruijnInitIndex) :: Binder DeBruijn) @?= []
    , testCase "Binder FakeNamedDeBruijn encodes as empty (zero-cost)" $
        flatBytes (Binder (toFake (DeBruijn deBruijnInitIndex)) :: Binder FakeNamedDeBruijn) @?= []
    , testCase "Binder Name encodes same as Name" $
        flatBytes (Binder (Name "x" (Unique 0)) :: Binder Name)
          @?= flatBytes (Name "x" (Unique 0))
    , testCase "Binder TyName encodes same as TyName" $
        flatBytes (Binder (TyName (Name "x" (Unique 0))) :: Binder TyName)
          @?= flatBytes (TyName (Name "x" (Unique 0)))
    , testCase "Binder NamedDeBruijn encodes same as NamedDeBruijn" $
        flatBytes (Binder (NamedDeBruijn "x" (Index 42)) :: Binder NamedDeBruijn)
          @?= flatBytes (NamedDeBruijn "x" (Index 42))
    , testCase "Binder NamedTyDeBruijn encodes same as NamedTyDeBruijn" $
        flatBytes (Binder (NamedTyDeBruijn (NamedDeBruijn "x" (Index 42))) :: Binder NamedTyDeBruijn)
          @?= flatBytes (NamedTyDeBruijn (NamedDeBruijn "x" (Index 42)))
    ]

-- | Roundtrip tests for newtype Binder wrappers (Name, TyName, NamedDeBruijn, NamedTyDeBruijn).
test_binderNewtypeRoundtrip :: TestTree
test_binderNewtypeRoundtrip =
  testGroup
    "Binder newtype roundtrip"
    [ testCase "Binder Name" $
        let v = Binder (Name "x" (Unique 0)) :: Binder Name
         in unflat (flat v) @?= Right v
    , testCase "Binder TyName" $
        let v = Binder (TyName (Name "x" (Unique 0))) :: Binder TyName
         in unflat (flat v) @?= Right v
    , testCase "Binder NamedDeBruijn" $
        let v = Binder (NamedDeBruijn "x" (Index 42)) :: Binder NamedDeBruijn
         in unflat (flat v) @?= Right v
    , testCase "Binder NamedTyDeBruijn" $
        let v = Binder (NamedTyDeBruijn (NamedDeBruijn "x" (Index 42))) :: Binder NamedTyDeBruijn
         in unflat (flat v) @?= Right v
    ]

{-| Roundtrip and stable byte test for a minimal UPLC program:
  (program 1.1.0 (con integer 0)) -}
test_uplcProgramFlat :: TestTree
test_uplcProgramFlat =
  testGroup
    "UPLC Program"
    [ testCase "minimal program roundtrip" $
        let encoded = flat (UnrestrictedProgram prog)
         in fmap unUnrestrictedProgram (unflat encoded) @?= Right prog
    , testCase "minimal program stable encoding" $
        flatBytes (UnrestrictedProgram prog) @?= [1, 1, 0, 72, 0, 0]
    ]
  where
    prog :: Program DeBruijn DefaultUni DefaultFun DefaultBuiltinPattern () =
      Program
        ()
        (Version 1 1 0)
        (Constant () (Some (ValueOf DefaultUniInteger (0 :: Integer))))

test_patternProgramFlat :: TestTree
test_patternProgramFlat =
  testGroup
    "UPLC Match Programs"
    [ testCase "version 1.2 match roundtrip" $
        let program = matchProg $ Version 1 2 0
         in unrestrictedDecode (flat $ UnrestrictedProgram program) @?= Right program
    , testCase "all default built-in pattern descriptors roundtrip" $
        mapM_
          (\pat -> unflat (flat pat) @?= (Right pat :: Either DecodeException DefaultBuiltinPattern))
          [ DefaultPatternWildcard
          , DefaultPatternCapture
          , DefaultPatternInteger (-42)
          , DefaultPatternInteger minBound
          , DefaultPatternInteger maxBound
          , DefaultPatternByteString "pattern-bytes"
          , DefaultPatternBool True
          , DefaultPatternUnit
          , DefaultPatternList emptyChildren
          , DefaultPatternPair
              DefaultPatternWildcard
              DefaultPatternCapture
          , DefaultPatternDataConstr maxBound emptyChildren
          , DefaultPatternDataMap emptyChildren
          , DefaultPatternDataList emptyChildren
          , DefaultPatternDataI Nothing
          , DefaultPatternDataB Nothing
          ]
    , testCase "version 1.2 match stable encoding" $
        flatBytes (UnrestrictedProgram $ matchProg (Version 1 2 0))
          @?= [1, 2, 0, 164, 128, 3, 88, 0, 136, 144, 42, 65, 32, 0, 0]
    , testCase "all default built-in pattern descriptors have stable encodings" $
        mapM_
          (\(pat, expected) -> flatBytes pat @?= expected)
          [ (DefaultPatternWildcard, [0])
          , (DefaultPatternCapture, [16])
          , (DefaultPatternInteger 0, [32, 0])
          , (DefaultPatternByteString mempty, [49, 0])
          , (DefaultPatternBool False, [64])
          , (DefaultPatternUnit, [80])
          , (DefaultPatternList emptyChildren, [96])
          ,
            ( DefaultPatternPair
                DefaultPatternWildcard
                DefaultPatternCapture
            , [112, 16]
            )
          , (DefaultPatternDataConstr 0 emptyChildren, [128, 0])
          , (DefaultPatternDataConstr 1 emptyChildren, [128, 16])
          , (DefaultPatternDataMap emptyChildren, [144])
          , (DefaultPatternDataList emptyChildren, [160])
          , (DefaultPatternDataI Nothing, [176])
          , (DefaultPatternDataB Nothing, [192])
          ]
    , testCase "match is rejected before version 1.2" $ do
        assertUnrestrictedRejects "pre-1.2 match program" $ matchProg (Version 1 1 0)
    , testCase "restricted decoder accepts match-alternative arity at its limit" $
        let withinLimit = wideMatchProg 3
         in restrictedDecode (flat $ UnrestrictedProgram withinLimit) @?= Right withinLimit
    , testCase "restricted decoder rejects oversized match-alternative arity" $
        assertRestrictedRejects "oversized match alternative" $
          wideMatchProg 4
    , testCase "restricted decoder rejects unavailable built-in pattern descriptor" $
        assertPatternRestrictedRejects "unavailable built-in pattern descriptor" $
          matchProg (Version 1 2 0)
    , testCase "reserved term tags are rejected" $
        mapM_ assertReservedTermTag [11 .. 15]
    , testCase "reserved default built-in pattern tags are rejected" $
        mapM_ assertReservedDefaultPatternTag [13 .. 15]
    , testCase "truncated built-in pattern descriptor payloads are rejected" $
        mapM_
          assertTruncatedDefaultPattern
          [ DefaultPatternInteger maxBound
          , DefaultPatternByteString $ BS.pack [1 .. 8]
          , DefaultPatternDataConstr maxBound emptyChildren
          ]
    ]
  where
    emptyChildren = Vector.empty

    matchProg
      :: Version
      -> Program DeBruijn DefaultUni DefaultFun DefaultBuiltinPattern ()
    matchProg version = Program () version matchBody

    nestedPattern :: DefaultBuiltinPattern
    nestedPattern =
      DefaultPatternDataList $
        Vector.singleton
          ( DefaultPatternDataConstr
              0
              (Vector.singleton DefaultPatternCapture)
          )

    matchBody :: Term DeBruijn DefaultUni DefaultFun DefaultBuiltinPattern ()
    matchBody =
      Match
        ()
        (Constant () $ Some (ValueOf DefaultUniInteger (0 :: Integer)))
        ( Vector.fromList
            [ (nestedPattern, Constant () $ Some (ValueOf DefaultUniInteger (42 :: Integer)))
            , (DefaultPatternWildcard, Constant () $ Some (ValueOf DefaultUniInteger (0 :: Integer)))
            ]
        )

    wideMatchProg
      :: Int
      -> Program DeBruijn DefaultUni DefaultFun DefaultBuiltinPattern ()
    wideMatchProg childCount =
      Program
        ()
        (Version 1 2 0)
        ( Match
            ()
            (Constant () $ Some (ValueOf DefaultUniInteger (0 :: Integer)))
            ( Vector.singleton
                ( DefaultPatternList $ Vector.replicate childCount DefaultPatternWildcard
                , Constant () $ Some (ValueOf DefaultUniInteger (0 :: Integer))
                )
            )
        )

    unrestrictedDecode
      :: BS.ByteString
      -> Either
           DecodeException
           (Program DeBruijn DefaultUni DefaultFun DefaultBuiltinPattern ())
    unrestrictedDecode = fmap unUnrestrictedProgram . unflat

    restrictedDecode
      :: BS.ByteString
      -> Either
           DecodeException
           (Program DeBruijn DefaultUni DefaultFun DefaultBuiltinPattern ())
    restrictedDecode =
      unflatWith $
        decodeProgram
          (const Nothing)
          (const Nothing)
          (const Nothing)
          (const checkPatternArity)

    patternRestrictedDecode
      :: BS.ByteString
      -> Either
           DecodeException
           (Program DeBruijn DefaultUni DefaultFun DefaultBuiltinPattern ())
    patternRestrictedDecode =
      unflatWith $
        decodeProgram
          (const Nothing)
          (const Nothing)
          (const Nothing)
          (const checkPatternDescriptor)

    checkPatternArity (DefaultPatternList children)
      | Vector.length children > 3 =
          Just "pattern has too many children"
    checkPatternArity _ = Nothing

    checkPatternDescriptor (DefaultPatternDataList _) = Just "data-list patterns are unavailable"
    checkPatternDescriptor _ = Nothing

    assertUnrestrictedRejects description program =
      case unrestrictedDecode . flat $ UnrestrictedProgram program of
        Left _ -> pure ()
        Right result -> assertFailure $ "decoded a " <> description <> ": " <> show result

    assertRestrictedRejects description program =
      case restrictedDecode . flat $ UnrestrictedProgram program of
        Left _ -> pure ()
        Right result -> assertFailure $ "decoded an " <> description <> ": " <> show result

    assertPatternRestrictedRejects description program =
      case patternRestrictedDecode . flat $ UnrestrictedProgram program of
        Left _ -> pure ()
        Right result -> assertFailure $ "decoded an " <> description <> ": " <> show result

    assertReservedTermTag tag =
      assertDecodeRejects
        ("reserved term tag " <> show tag)
        ( unflatWith
            ( decodeTerm
                (Version 1 2 0)
                (const Nothing)
                (const Nothing)
                (const Nothing)
                (const Nothing)
            )
            (flat $ RawTag 4 tag)
            :: Either
                 DecodeException
                 (Term DeBruijn DefaultUni DefaultFun DefaultBuiltinPattern ())
        )

    assertReservedDefaultPatternTag tag =
      assertDecodeRejects
        ("reserved default built-in pattern tag " <> show tag)
        ( unflat (flat $ RawTag 4 tag)
            :: Either DecodeException DefaultBuiltinPattern
        )

    assertTruncatedDefaultPattern pat =
      let encoded = flat pat
          truncated = BS.take (BS.length encoded - 2) encoded
       in assertDecodeRejects
            ("truncated default built-in pattern " <> show pat)
            (unflat truncated :: Either DecodeException DefaultBuiltinPattern)

    assertDecodeRejects description result =
      case result of
        Left _ -> pure ()
        Right value -> assertFailure $ "decoded " <> description <> ": " <> show value

test_matchVersionRemainsExperimental :: TestTree
test_matchVersionRemainsExperimental =
  testCase "Plutus Core 1.2 Match remains experimental" $ do
    latestVersion @?= plcVersion110
    assertBool "Plutus Core 1.2 unexpectedly appears in knownVersions" $
      plcVersion120 `notElem` knownVersions

test_flat :: TestTree
test_flat =
  testGroup
    "FlatProp"
    [ test_deBruijnIso
    , test_fakeIso
    , test_deBruijnTripping
    , test_fakeTripping
    , test_binderDeBruijn
    , test_binderFake
    , test_binderStaticEncoding
    , test_binderNewtypeRoundtrip
    , test_uplcProgramFlat
    , test_patternProgramFlat
    , test_matchVersionRemainsExperimental
    , test_canonicalData
    , test_canonicalByteString
    , test_nonCanonicalByteStringDecoding
    ]

-- Helpers

flatBytes :: Flat a => a -> [Word8]
flatBytes = asBytes . bits

initB :: Binder DeBruijn
initB = Binder $ DeBruijn deBruijnInitIndex

-- orphans for QuickCheck generation
deriving via Word64 instance Arbitrary DeBruijn
instance Arbitrary FakeNamedDeBruijn where
  arbitrary = toFake <$> arbitrary -- via debruijn
deriving newtype instance Arbitrary (Binder DeBruijn)
deriving newtype instance Arbitrary (Binder FakeNamedDeBruijn)
