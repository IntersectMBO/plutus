{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

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
import Test.Tasty.Hedgehog
import Test.Tasty.HUnit

-- | The `SrcSpan` of a parsed `Term` should not including trailing whitespaces.
propTermSrcSpan :: Property
propTermSrcSpan = property $ do
    term <- _progTerm <$>
        forAllWith display (runAstGen $ regenConstantsUntil isSerialisable =<< genProgram)
    let code = display (term :: Term TyName Name DefaultUni DefaultFun ())
    let (endingLine, endingCol) = length &&& T.length . last $ T.lines code
    trailingSpaces <- forAll $ Gen.text (Range.linear 0 10) (Gen.element [' ', '\n'])
    case runQuoteT . parseTerm $ code <> trailingSpaces of
        Right parsed ->
            let sp = termAnn parsed
             in (srcSpanELine sp, srcSpanECol sp) === (endingLine, endingCol + 1)
        Left err -> annotate (display err) >> failure

expectParserSuccess :: T.Text -> Assertion
expectParserSuccess code = case runQuoteT (parseTerm code) of
  Right _ -> pure ()
  Left _  -> assertFailure $ "Unexpected failure when parsing term: " <> T.unpack code

expectParserFailure :: T.Text -> Assertion
expectParserFailure code = case runQuoteT (parseTerm code) of
  Right _ -> assertFailure $ "Unexpected success when parsing term: " <> T.unpack code
  Left _  -> pure ()

parseValueInvalidCurrency :: Assertion
parseValueInvalidCurrency = do
  expectParserFailure code
  where
    -- Currency is 33 bytes
    code = "(con value \
       \[ ( #616161616161616161616161616161616161616161616161616161616161616161\
       \, [ ( #6161616161616161616161616161616161616161616161616161616161616161\
       \    , -100 ) ] ) ])"

parseValueInvalidToken :: Assertion
parseValueInvalidToken = do
  expectParserFailure code
  where
    -- Token is 33 bytes
    code = "(con value \
       \[ ( #6161616161616161616161616161616161616161616161616161616161616161\
       \, [ ( #616161616161616161616161616161616161616161616161616161616161616161\
       \    , -100 ) ] ) ])"

parseValueValid :: Assertion
parseValueValid = do
  expectParserSuccess code
  where
    -- Both currency and token are 32 bytes
    code = "(con value \
       \[ ( #6161616161616161616161616161616161616161616161616161616161616161\
       \, [ ( #6161616161616161616161616161616161616161616161616161616161616161\
       \    , -100 ) ] ) ])"

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
        ]
