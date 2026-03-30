{-# LANGUAGE OverloadedStrings #-}

module Flat.Spec (tests) where

import Data.ByteString.Lazy.Char8 qualified as LBS
import Data.Set qualified as Set
import Data.Word (Word8)
import PlutusCore
  ( Kind (..)
  , Name (..)
  , Normalized (..)
  , TyName (..)
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
import PlutusCore.Default (DefaultFun (..), DefaultUni (..))
import PlutusCore.Flat qualified as Flat
import PlutusCore.Flat.Bits (asBytes, bits)
import Test.Tasty
import Test.Tasty.Golden (goldenVsStringDiff)
import Test.Tasty.HUnit
import Universe (SomeTypeIn (..))

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
          , enc "SomeTypeIn DefaultUniInteger" (SomeTypeIn DefaultUniInteger)
          ]
    )

-- | Roundtrip tests for TPLC types.
test_flatRoundtrip :: TestTree
test_flatRoundtrip =
  testGroup
    "Flat roundtrip"
    [ testCase "SrcSpan" $
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
        let v = Version 1 1 0
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
    , test_flatRoundtrip
    , test_flatNewtypeWrappers
    ]
