-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

-- | UPLC property tests (pretty-printing\/parsing and binary encoding\/decoding).
module Generators.Spec where

import PlutusPrelude (display, fold, void, (&&&))

import Control.Lens (view)
import Control.Monad (unless)
import Data.Text (Text)
import Data.Text qualified as T
import Hedgehog (annotate, annotateShow, failure, property, tripping, (===))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import PlutusCore (Name)
import PlutusCore.Annotation (SrcSpan (..))
import PlutusCore.Default (DefaultFun, DefaultUni)
import PlutusCore.Error (ParserErrorBundle (ParseErrorB))
import PlutusCore.Flat (flat, unflat)
import PlutusCore.Generators.Hedgehog (forAllPretty)
import PlutusCore.Generators.Hedgehog.AST (runAstGen)
import PlutusCore.Parser (defaultUni, parseGen)
import PlutusCore.Pretty (displayPlc)
import PlutusCore.Quote (runQuoteT)
import PlutusCore.Test (isSerialisable)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))
import Test.Tasty.Hedgehog (testPropertyNamed)
import Text.Megaparsec (errorBundlePretty)
import UntypedPlutusCore (Program)
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Core.Type (progTerm, termAnn)
import UntypedPlutusCore.Generators.Hedgehog.AST (genProgram, regenConstantsUntil)
import UntypedPlutusCore.Parser (parseProgram, parseTerm)

propFlat :: TestTree
propFlat = testPropertyNamed "Flat" "Flat" $ property $ do
  prog <-
    forAllPretty . runAstGen $
      regenConstantsUntil isSerialisable =<< genProgram @DefaultFun
  tripping prog (flat . UPLC.UnrestrictedProgram) (fmap UPLC.unUnrestrictedProgram . unflat)

propParser :: TestTree
propParser = testPropertyNamed "Parser" "parser" $ property $ do
  prog <- forAllPretty (runAstGen $ regenConstantsUntil isSerialisable =<< genProgram)
  tripping prog displayPlc (fmap void . parseProg)
  where
    parseProg
      :: T.Text -> Either ParserErrorBundle (Program Name DefaultUni DefaultFun SrcSpan)
    parseProg = runQuoteT . parseProgram

-- | The `SrcSpan` of a parsed `Term` should not including trailing whitespaces.
propTermSrcSpan :: TestTree
propTermSrcSpan = testPropertyNamed
  "parser captures ending positions correctly"
  "propTermSrcSpan"
  . property
  $ do
    code <- genRandomCode
    annotateShow code
    let (endingLine, endingCol) = getCodeEndingLineAndCol code
    result <- parseTermWithTrailingSpace code
    case result of
      Right term -> do
        let (endingLine', endingCol') = getTermEndingLineAndCol term
        (endingLine', endingCol') === (endingLine, endingCol + 1)
      Left err ->
        handleParseError err
  where
    genRandomCode =
      display
        <$> forAllPretty
          ( view progTerm
              <$> runAstGen (regenConstantsUntil isSerialisable =<< genProgram @DefaultFun)
          )

    getCodeEndingLineAndCol code = (length &&& T.length . last) (T.lines code)

    parseTermWithTrailingSpace code = do
      trailingSpaces <- genTrailingSpaces
      return $ runQuoteT $ parseTerm (code <> trailingSpaces)

    genTrailingSpaces = forAllPretty $ Gen.text (Range.linear 0 10) (Gen.element [' ', '\n'])

    getTermEndingLineAndCol term = do
      let sp = termAnn term
      (srcSpanELine sp, srcSpanECol sp)

    handleParseError err = annotate (display err) >> failure

propUnit :: TestTree
propUnit =
  testCase "Unit" $
    fold
      [ pTerm "(con bool True)"
          @?= "(con bool True)"
      , pTerm "(con (list bool) [True, False])"
          @?= "(con (list bool) [True,False])"
      , pTerm "(con (pair unit (list integer)) ((),[1,2,3]))"
          @?= "(con (pair unit (list integer)) ((), [1,2,3]))"
      , pTerm "(con (list (pair string bool)) [(\"abc\", True), (\"def\", False)])"
          @?= "(con (list (pair string bool)) [(\"abc\", True), (\"def\", False)])"
      , pTerm "(con string \"abc\")"
          @?= "(con string \"abc\")"
      ]
  where
    pTerm :: String -> Text
    pTerm =
      either (error . display) display
        . runQuoteT
        . parseTerm
        . T.pack

propDefaultUni :: TestTree
propDefaultUni =
  testCase "DefaultUni" $
    fold
      [ pDefaultUni "bool" @?= "bool"
      , pDefaultUni "list" @?= "list"
      , pDefaultUni "(list integer)" @?= "(list integer)"
      , pDefaultUni "(pair (list bool))" @?= "(pair (list bool))"
      , pDefaultUni "(pair (list unit) integer)" @?= "(pair (list unit) integer)"
      , pDefaultUni "(list (pair unit integer))" @?= "(list (pair unit integer))"
      , pDefaultUni "(pair unit (pair bool integer))" @?= "(pair unit (pair bool integer))"
      ]
  where
    pDefaultUni :: String -> Text
    pDefaultUni =
      either (error . display) display
        . runQuoteT
        . parseGen defaultUni
        . T.pack

{-| Test that parser errors for list element type mismatches point to the correct location.
This uses the exact example from the issue report. -}
propListElementErrorLocation :: TestTree
propListElementErrorLocation =
  testCase "List element error location" $ do
    let code =
          T.unlines
            [ "(program 1.1.0 "
            , "["
            , " (force (builtin mkCons)) (con integer 4) (con (list integer) [true]) ]"
            , ")"
            ]
        expectedErrorParts = ["unexpected 't'", "expecting '+', '-', ']', or integer"]
    case runQuoteT (parseProgram code) of
      Right _ -> error "Expected parse error, but parsing succeeded"
      Left (ParseErrorB errBundle) -> do
        let errMsg = T.pack $ errorBundlePretty errBundle
        let hasAllParts = all (`T.isInfixOf` errMsg) expectedErrorParts
        unless hasAllParts $
          error $
            "Error message does not match expected format.\n"
              <> "Expected to contain: "
              <> show expectedErrorParts
              <> "\nGot error message:\n"
              <> T.unpack errMsg

{-| Test that parser errors for typos in type names point to the correct location.
This tests the case where "boot" is used instead of "bool". -}
propTypeNameTypoErrorLocation :: TestTree
propTypeNameTypoErrorLocation =
  testCase "Type name typo error location" $ do
    let code =
          T.unlines
            [ "(program 1.1.0"
            , "[ (builtin integerToByteString) (con boot True) (con integer 0) (con integer 712372356934756347862573452345342345) ]"
            , ")"
            ]
        expectedErrorParts = ["Unknown type", "expected", "bool"]
    case runQuoteT (parseProgram code) of
      Right _ -> error "Expected parse error, but parsing succeeded"
      Left (ParseErrorB errBundle) -> do
        let errMsg = T.pack $ errorBundlePretty errBundle
        let hasAllParts = all (`T.isInfixOf` errMsg) expectedErrorParts
        unless hasAllParts $
          error $
            "Error message does not match expected format.\n"
              <> "Expected to contain: "
              <> show expectedErrorParts
              <> "\nGot error message:\n"
              <> T.unpack errMsg

test_parsing :: TestTree
test_parsing =
  testGroup
    "Parsing"
    [ propFlat
    , propParser
    , propTermSrcSpan
    , propUnit
    , propDefaultUni
    , propListElementErrorLocation
    , propTypeNameTypoErrorLocation
    ]
