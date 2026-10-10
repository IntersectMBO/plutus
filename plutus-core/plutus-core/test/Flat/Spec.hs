{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Flat.Spec (tests) where

import Data.ByteString.Lazy.Char8 qualified as LBS
import Data.Either (isLeft)
import Data.Set qualified as Set
import Data.Word (Word8)
import PlutusCore
  ( Kind (..)
  , Name (..)
  , Normalized (..)
  , TyName (..)
  , Type (..)
  , Unique (..)
  , Version (..)
  )
import PlutusCore.Annotation (SrcSpan (..), SrcSpans (..))
import PlutusCore.DeBruijn
  ( DeBruijn (..)
  , Index (..)
  , NamedDeBruijn (..)
  , NamedTyDeBruijn (..)
  , TyDeBruijn (..)
  , toFake
  )
import PlutusCore.Default
  ( DefaultFun (..)
  , DefaultUni (..)
  )
import PlutusCore.Flat qualified as Flat
import PlutusCore.Flat.Bits (asBytes, bits)
import PlutusCore.Flat.Encoder (encodeListWith)
import PlutusCore.FlatInstances (safeEncodeBits)
import PlutusCore.MkPlc (mkTyBuiltin, mkTyBuiltinOf)
import Test.Tasty
import Test.Tasty.Golden (goldenVsStringDiff)
import Test.Tasty.HUnit
import Universe (Closed (..), Some (..))

-- Raw historical tag lists, including malformed inputs that native tags cannot express.
newtype LegacyConstantType = LegacyConstantType [Word8]

instance Flat.Flat LegacyConstantType where
  encode (LegacyConstantType tags) = encodeListWith (safeEncodeBits 4) tags
  size (LegacyConstantType tags) acc = acc + 5 * length tags + 1
  decode = fail "LegacyConstantType is only used to produce compatibility fixtures"

test_constantTagCompatibility :: TestTree
test_constantTagCompatibility =
  testGroup
    "constant tag compatibility"
    [ testGroup
        "stable encoding"
        [ testCase label $ do
            encodeUni tag @?= tags
            Flat.flat (Some tag) @?= Flat.flat (LegacyConstantType tags)
            Flat.unflat (Flat.flat $ LegacyConstantType tags) @?= Right (Some tag)
        | (label, tags, Some tag) <-
            [ ("list", [7, 5, 0], Some $ DefaultUniList DefaultUniInteger)
            , ("pair", [7, 7, 6, 0, 4], Some $ DefaultUniPair DefaultUniInteger DefaultUniBool)
            , ("array", [7, 12, 3], Some $ DefaultUniArray DefaultUniUnit)
            ,
              ( "nested"
              , [7, 5, 7, 7, 6, 0, 7, 12, 4]
              , Some $ DefaultUniList $ DefaultUniPair DefaultUniInteger $ DefaultUniArray DefaultUniBool
              )
            ]
        ]
    , testGroup
        "reject incomplete or invalid tags"
        [ testCase (show tags) $
            assertBool "Flat decoder accepted an invalid constant type" $
              isLeft $
                Flat.unflat @(Some DefaultUni) $
                  Flat.flat $
                    LegacyConstantType tags
        | tags <-
            [ []
            , [5]
            , [6]
            , [12]
            , [7]
            , [7, 5]
            , [7, 6, 0]
            , [7, 7, 6, 0]
            , [7, 0, 4]
            , [7, 5, 5]
            , [0, 4]
            , [7, 5, 0, 4]
            , [14]
            , [15]
            ]
        ]
    ]

flatBytes :: Flat.Flat a => a -> [Word8]
flatBytes = asBytes . bits

enc :: Flat.Flat a => String -> a -> String
enc label v = label ++ " = " ++ show (flatBytes v)

{-| Stable byte encoding tests for TPLC types.
These capture the exact byte representation to detect encoding changes.
Use @cabal test plutus-core-test --test-options --accept@ to update golden files. -}
test_flatStaticEncoding :: TestTree
test_flatStaticEncoding =
  goldenVsStringDiff
    "Flat stable encoding"
    (\expected actual -> ["diff", "-u", expected, actual])
    "plutus-core/test/Flat/golden/encoding-stability.golden"
    ( pure . LBS.pack $
        unlines
          [ "-- Core types"
          , enc "Version 1 1 0" (Version 1 1 0)
          , enc "Name \"x\" (Unique 0)" (Name "x" (Unique 0))
          , enc "Kind: Type ()" (Type () :: Kind ())
          , enc "DeBruijn (Index 1)" (DeBruijn (Index 1))
          , enc "NamedDeBruijn \"x\" (Index 42)" (NamedDeBruijn "x" (Index 42))
          , enc "Index 1" (Index 1)
          , enc "SrcSpan \"f\" 1 2 3 4" (SrcSpan "f" 1 2 3 4)
          , let sp = SrcSpan "f" 1 2 3 4
             in enc "SrcSpans (Set.fromList [sp])" (SrcSpans (Set.fromList [sp]))
          , ""
          , "-- DefaultFun"
          , enc "AddInteger" AddInteger
          , enc "SubtractInteger" SubtractInteger
          , ""
          , "-- DefaultUni"
          , enc "SomeTypeIn DefaultUniInteger" (Some DefaultUniInteger)
          ]
    )

-- | Roundtrip tests for TPLC types.
test_flatRoundtrip :: TestTree
test_flatRoundtrip =
  testGroup
    "Flat roundtrip"
    [ testGroup
        "built-in types"
        [ testCase label $ Flat.unflat (Flat.flat ty) @?= Right ty
        | (label, ty) <-
            [ ("integer", mkTyBuiltin @_ @Integer ())
            , ("list head", mkTyBuiltin @_ @[] ())
            , ("partially applied pair", TyApp () (mkTyBuiltin @_ @(,) ()) (mkTyBuiltin @_ @Integer ()))
            ,
              ( "nested list/pair/array"
              , mkTyBuiltinOf () $
                  DefaultUniList $
                    DefaultUniPair DefaultUniInteger $
                      DefaultUniArray DefaultUniBool
              )
            ]
              :: [(String, Type TyName DefaultUni ())]
        ]
    , testCase "application annotations" $
        let ty = TyApp (1 :: Int) (mkTyBuiltin @_ @[] 2) (mkTyBuiltin @_ @Integer 3) :: Type TyName DefaultUni Int
         in Flat.unflat (Flat.flat ty) @?= Right ty
    , testCase "SrcSpan" $
        let sp = SrcSpan "f" 1 2 3 4
         in Flat.unflat (Flat.flat sp) @?= Right sp
    , testCase "SrcSpans" $
        let sp = SrcSpan "test.hs" 1 2 3 4
            sps = SrcSpans (Set.fromList [sp])
         in Flat.unflat (Flat.flat sps) @?= Right sps
    , testCase "NamedDeBruijn" $
        let ndb = NamedDeBruijn "x" (Index 42)
         in Flat.unflat (Flat.flat ndb) @?= Right ndb
    , testCase "Version" $
        let v = Version 1 2 0
         in Flat.unflat (Flat.flat v) @?= Right v
    , testCase "Name" $
        let n = Name "x" (Unique 0)
         in Flat.unflat (Flat.flat n) @?= Right n
    , testCase "Kind Type ()" $
        let k = Type () :: Kind ()
         in Flat.unflat (Flat.flat k) @?= Right k
    ]

{-| Tests for newtype wrappers: verify they encode the same as their
underlying type and roundtrip correctly.
Note: Binder tests are in the UPLC testlib (Flat.Spec) since Binder
is not publicly exported from plutus-core. -}
test_flatNewtypeWrappers :: TestTree
test_flatNewtypeWrappers =
  testGroup
    "Flat newtype wrappers"
    [ testGroup
        "Roundtrip"
        [ testCase "TyName" $
            let v = TyName (Name "x" (Unique 0))
             in Flat.unflat (Flat.flat v) @?= Right v
        , testCase "Unique" $
            let v = Unique 42
             in Flat.unflat (Flat.flat v) @?= Right v
        , testCase "TyDeBruijn" $
            let v = TyDeBruijn (DeBruijn (Index 1))
             in Flat.unflat (Flat.flat v) @?= Right v
        , testCase "NamedTyDeBruijn" $
            let v = NamedTyDeBruijn (NamedDeBruijn "x" (Index 42))
             in Flat.unflat (Flat.flat v) @?= Right v
        , testCase "Normalized" $
            let v = Normalized True
             in Flat.unflat (Flat.flat v) @?= Right v
        , testCase "FakeNamedDeBruijn" $
            let v = toFake (DeBruijn (Index 1))
             in Flat.unflat (Flat.flat v) @?= Right v
        ]
    , testGroup
        "Encoding delegation"
        [ testCase "TyName encodes same as Name" $
            flatBytes (TyName (Name "x" (Unique 0)))
              @?= flatBytes (Name "x" (Unique 0))
        , testCase "TyDeBruijn encodes same as DeBruijn" $
            flatBytes (TyDeBruijn (DeBruijn (Index 1)))
              @?= flatBytes (DeBruijn (Index 1))
        , testCase "NamedTyDeBruijn encodes same as NamedDeBruijn" $
            flatBytes (NamedTyDeBruijn (NamedDeBruijn "x" (Index 42)))
              @?= flatBytes (NamedDeBruijn "x" (Index 42))
        , testCase "FakeNamedDeBruijn encodes same as DeBruijn" $
            flatBytes (toFake (DeBruijn (Index 1)))
              @?= flatBytes (DeBruijn (Index 1))
        ]
    ]

-- | Combined test tree.
tests :: TestTree
tests =
  testGroup
    "Flat serialization"
    [ test_flatStaticEncoding
    , test_constantTagCompatibility
    , test_flatRoundtrip
    , test_flatNewtypeWrappers
    ]
