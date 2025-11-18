module PlutusIR.Core.Tests where

import PlutusCore qualified as PLC
import PlutusCore.Pretty
import PlutusIR
import PlutusIR.Parser (pTerm)
import PlutusIR.Test

import Test.Tasty
import Test.Tasty.Extras

import Data.Functor
import PlutusCore.Flat

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
