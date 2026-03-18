module PlutusIR.Core.Tests where

import PlutusCore qualified as PLC
import PlutusCore.Pretty
import PlutusIR
import PlutusIR.Parser (pTerm)
import PlutusIR.Test

import Test.Tasty
import Test.Tasty.Extras
import Test.Tasty.HUnit

import Data.Functor
import Data.Word (Word8)
import PlutusCore.Flat
import PlutusCore.Flat.Bits (asBytes, bits)

test_prettyprinting :: TestTree
test_prettyprinting =
  runTestNested ["plutus-ir", "test", "PlutusIR", "Core", "prettyprinting"] $
    map
      (goldenPir id pTerm)
      [ "basic"
      , "maybe"
      ]

test_prettyprintingReadable :: TestTree
test_prettyprintingReadable =
  runTestNested ["plutus-ir", "test", "PlutusIR", "Core", "prettyprintingReadable"] $
    map
      (goldenPirDoc prettyReadableSimple pTerm)
      [ "basic"
      , "maybe"
      , "letInLet"
      , "letDep"
      , "listMatch"
      , "idleAll"
      , "some"
      , "even3"
      , "stupidZero"
      , "mutuallyRecursiveValues"
      , "errorBinding"
      , "some"
      , "stupidZero"
      , "recursiveTypeBind"
      ]

test_serialization :: TestTree
test_serialization =
  runTestNested ["plutus-ir", "test", "PlutusIR", "Core", "serialization"] $
    map
      (goldenPir roundTripPirTerm pTerm)
      [ "serializeBasic"
      , "serializeMaybePirTerm"
      , "serializeEvenOdd"
      , "serializeListMatch"
      ]

roundTripPirTerm
  :: Term TyName Name PLC.DefaultUni PLC.DefaultFun a
  -> Term TyName Name PLC.DefaultUni PLC.DefaultFun ()
roundTripPirTerm = decodeOrError . unflat . flat . void
  where
    decodeOrError (Right tm) = tm
    decodeOrError (Left err) = error (show err)

test_flatStaticEncoding :: TestTree
test_flatStaticEncoding =
  testGroup
    "Flat stable encoding"
    [ testCase "NonRec" $ flatBytes NonRec @?= [0]
    , testCase "Rec" $ flatBytes Rec @?= [128]
    , testCase "NonStrict" $ flatBytes NonStrict @?= [0]
    , testCase "Strict" $ flatBytes Strict @?= [128]
    ]
  where
    flatBytes :: Flat a => a -> [Word8]
    flatBytes = asBytes . bits
