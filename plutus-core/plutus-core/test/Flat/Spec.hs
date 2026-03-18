{-# LANGUAGE OverloadedStrings #-}

module Flat.Spec (tests) where

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
import Test.Tasty.HUnit
import Universe (SomeTypeIn (..))

flatBytes :: Flat.Flat a => a -> [Word8]
flatBytes = asBytes . bits

{-| Stable byte encoding tests for TPLC types.
These capture the exact byte representation to detect encoding changes. -}
test_flatStaticEncoding :: TestTree
test_flatStaticEncoding =
  testGroup
    "Flat stable encoding"
    [ testGroup
        "Core types"
        [ testCase "Version 1 1 0" $
            flatBytes (Version 1 1 0) @?= [1, 1, 0]
        , testCase "Name \"x\" (Unique 0)" $
            flatBytes (Name "x" (Unique 0)) @?= [1, 1, 120, 0, 0]
        , testCase "Kind: Type ()" $
            flatBytes (Type () :: Kind ()) @?= [0]
        , testCase "DeBruijn (Index 1)" $
            flatBytes (DeBruijn (Index 1)) @?= [1]
        , testCase "NamedDeBruijn \"x\" (Index 42)" $
            flatBytes (NamedDeBruijn "x" (Index 42)) @?= [1, 1, 120, 0, 42]
        , testCase "Index 1" $
            flatBytes (Index 1) @?= [1]
        , testCase "SrcSpan" $
            flatBytes (SrcSpan "f" 1 2 3 4) @?= [179, 0, 129, 1, 130, 0]
        , testCase "SrcSpans" $
            let sp = SrcSpan "f" 1 2 3 4
             in flatBytes (SrcSpans (Set.fromList [sp])) @?= [217, 128, 64, 128, 193, 0]
        ]
    , testGroup
        "DefaultFun"
        [ testCase "AddInteger" $
            flatBytes AddInteger @?= [0]
        , testCase "SubtractInteger" $
            flatBytes SubtractInteger @?= [2]
        ]
    , testGroup
        "DefaultUni"
        [ testCase "SomeTypeIn DefaultUniInteger" $
            flatBytes (SomeTypeIn DefaultUniInteger) @?= [128]
        ]
    ]

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
