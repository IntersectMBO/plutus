module PlutusIR.Core.Tests where

import PlutusCore qualified as PLC
import PlutusCore.Pretty
import PlutusIR
import PlutusIR.Parser (pTerm)
import PlutusIR.Test

import Test.Tasty
import Test.Tasty.Extras

import Control.Exception (ErrorCall (..), evaluate, try)
import Data.Functor
import Data.List (isPrefixOf)
import PlutusCore.Flat
import PlutusIR.Generators.QuickCheck (genTypeAndTerm_)
import Test.QuickCheck (Property, counterexample, discard, ioProperty, withMaxSuccess)
import Test.Tasty.QuickCheck qualified as QC

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

test_flatRoundTrip :: TestTree
test_flatRoundTrip = QC.testProperty "PIR Flat round-trip" flatRoundTripProperty

flatRoundTripProperty :: Property
flatRoundTripProperty = withMaxSuccess 200 $
  QC.forAll genTypeAndTerm_ $ \(_ty, tm) ->
    ioProperty $ do
      result <- try (evaluate (flat tm))
      pure $ case result of
        -- BLS12_381 curve points don't support Flat encoding
        Left (ErrorCall msg)
          | "Flat encoding is not supported" `isPrefixOf` msg -> discard
        Left (ErrorCall msg) -> counterexample msg False
        Right bs -> case unflat bs of
          Left err -> counterexample (show err) False
          Right tm' ->
            let bs' = flat (tm' :: Term TyName Name PLC.DefaultUni PLC.DefaultFun ())
             in counterexample "Re-encoded bytes differ" (bs == bs')

test_flatProgramRoundTrip :: TestTree
test_flatProgramRoundTrip =
  QC.testProperty "PIR Program Flat round-trip" $
    withMaxSuccess 50 $
      QC.forAll genTypeAndTerm_ $ \(_ty, tm) ->
        ioProperty $ do
          let prog = Program () PLC.latestVersion (void tm)
          result <- try (evaluate (flat prog))
          pure $ case result of
            Left (ErrorCall msg)
              | "Flat encoding is not supported" `isPrefixOf` msg -> discard
            Left (ErrorCall msg) -> counterexample msg False
            Right bs -> case unflat bs of
              Left err -> counterexample (show err) False
              Right prog' ->
                let bs' = flat (prog' :: Program TyName Name PLC.DefaultUni PLC.DefaultFun ())
                 in counterexample "Re-encoded bytes differ" (bs == bs')
