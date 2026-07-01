{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

-- | Tests for TPLC parser.
module Parser.Spec (tests) where

import PlutusCore
import PlutusCore.Generators.Hedgehog.AST
import PlutusCore.Test (isSerialisable)
import PlutusPrelude

import Data.Text qualified as T
import Hedgehog hiding (Var)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Hedgehog

-- | The `SrcSpan` of a parsed `Term` should not including trailing whitespaces.
propTermSrcSpan :: Property
propTermSrcSpan = property $ do
  term <-
    _progTerm
      <$> forAllWith display (runAstGen $ regenConstantsUntil isSerialisable =<< genProgram)
  let code = display (term :: Term TyName Name DefaultUni DefaultFun ())
  let (endingLine, endingCol) = length &&& T.length . last $ T.lines code
  trailingSpaces <- forAll $ Gen.text (Range.linear 0 10) (Gen.element [' ', '\n'])
  case runQuoteT . parseTerm $ code <> trailingSpaces of
    Right parsed ->
      let sp = getAnn parsed
       in (srcSpanELine sp, srcSpanECol sp) === (endingLine, endingCol + 1)
    Left err -> annotate (display err) >> failure

expectParserSuccess :: T.Text -> Assertion
expectParserSuccess code = case runQuoteT (parseTerm code) of
  Right _ -> pure ()
  Left _ -> assertFailure $ "Unexpected failure when parsing term: " <> T.unpack code

expectParserFailure :: T.Text -> Assertion
expectParserFailure code = case runQuoteT (parseTerm code) of
  Right _ -> assertFailure $ "Unexpected success when parsing term: " <> T.unpack code
  Left _ -> pure ()

parseValueInvalidCurrency :: Assertion
parseValueInvalidCurrency = do
  expectParserFailure code
  where
    -- Currency is 33 bytes
    code =
      "(con value \
      \[ ( #616161616161616161616161616161616161616161616161616161616161616161\
      \, [ ( #6161616161616161616161616161616161616161616161616161616161616161\
      \    , -100 ) ] ) ])"

parseValueInvalidToken :: Assertion
parseValueInvalidToken = do
  expectParserFailure code
  where
    -- Token is 33 bytes
    code =
      "(con value \
      \[ ( #6161616161616161616161616161616161616161616161616161616161616161\
      \, [ ( #616161616161616161616161616161616161616161616161616161616161616161\
      \    , -100 ) ] ) ])"

parseValueValid :: Assertion
parseValueValid = do
  expectParserSuccess code
  where
    -- Both currency and token are 32 bytes
    code =
      "(con value \
      \[ ( #6161616161616161616161616161616161616161616161616161616161616161\
      \, [ ( #6161616161616161616161616161616161616161616161616161616161616161\
      \    , -100 ) ] ) ])"

parseValueAscendingCurrencies :: Assertion
parseValueAscendingCurrencies =
  expectParserSuccess "(con value [ ( #01, [ ( #01, 1 ) ] ), ( #02, [ ( #01, 1 ) ] ) ])"

parseValueNonAscendingCurrencies :: Assertion
parseValueNonAscendingCurrencies =
  expectParserFailure "(con value [ ( #02, [ ( #01, 1 ) ] ), ( #01, [ ( #01, 1 ) ] ) ])"

parseValueEqualCurrencies :: Assertion
parseValueEqualCurrencies =
  expectParserFailure "(con value [ ( #01, [ ( #01, 1 ) ] ), ( #01, [ ( #02, 1 ) ] ) ])"

parseValueAscendingTokens :: Assertion
parseValueAscendingTokens =
  expectParserSuccess "(con value [ ( #01, [ ( #01, 1 ), ( #02, 1 ) ] ) ])"

parseValueNonAscendingTokens :: Assertion
parseValueNonAscendingTokens =
  expectParserFailure "(con value [ ( #01, [ ( #02, 1 ), ( #01, 1 ) ] ) ])"

parseValueEqualTokens :: Assertion
parseValueEqualTokens =
  expectParserFailure "(con value [ ( #01, [ ( #01, 1 ), ( #01, 2 ) ] ) ])"

tests :: TestTree
tests =
  testGroup
    "parsing"
    [ testPropertyNamed
        "parser captures ending positions correctly"
        "propTermSrcSpan"
        propTermSrcSpan
    , testCase
        "parser of Value should fail upon invalid currency"
        parseValueInvalidCurrency
    , testCase
        "parser of Value should fail upon invalid token"
        parseValueInvalidToken
    , testCase
        "parser of Value should succeed"
        parseValueValid
    , testCase
        "parser of Value should succeed with ascending currency symbols"
        parseValueAscendingCurrencies
    , testCase
        "parser of Value should fail with non-ascending currency symbols"
        parseValueNonAscendingCurrencies
    , testCase
        "parser of Value should fail with equal (non-strictly-ascending) currency symbols"
        parseValueEqualCurrencies
    , testCase
        "parser of Value should succeed with ascending token names"
        parseValueAscendingTokens
    , testCase
        "parser of Value should fail with non-ascending token names"
        parseValueNonAscendingTokens
    , testCase
        "parser of Value should fail with equal (non-strictly-ascending) token names"
        parseValueEqualTokens
    , testCase
        "multi-arg application has per-argument spans on inner nodes"
        multiArgSpans
    ]

{-| Test that inner Apply nodes get per-argument spans, not the bracket span.
For @[ (con integer 1) (con integer 2) (con integer 3) ]@, the outer Apply
should have the bracket span, but the inner Apply should have the span of
its argument @(con integer 2)@, NOT the bracket span. -}
multiArgSpans :: Assertion
multiArgSpans = do
  let code = "[ (con integer 1) (con integer 2) (con integer 3) ]"
  case runQuoteT (parseTerm code) of
    Left err -> assertFailure $ "parse failed: " <> show err
    Right parsed ->
      case parsed of
        Apply outerAnn (Apply innerAnn _ _) _ -> do
          -- outer should have the bracket span (col 1 to col 52)
          assertBool
            "outer span should start at col 1"
            (srcSpanSCol outerAnn == 1)
          -- inner should NOT have the same span as outer
          assertBool
            ("inner Apply should have a different span than outer, but both are: " <> show outerAnn)
            (outerAnn /= innerAnn)
          -- inner span should start after col 1 (it's the span of the 2nd arg)
          assertBool
            ("inner Apply span should not start at col 1, got: " <> show innerAnn)
            (srcSpanSCol innerAnn /= 1)
        other -> assertFailure $ "expected nested Apply, got: " <> show other
