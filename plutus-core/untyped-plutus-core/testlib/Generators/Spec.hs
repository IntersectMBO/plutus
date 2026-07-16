-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

-- | UPLC property tests (pretty-printing\/parsing and binary encoding\/decoding).
module Generators.Spec where

import PlutusPrelude (display, fold, getAnn, void, (&&&))

import Control.Lens (view)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector qualified as Vector
import Hedgehog (annotate, annotateShow, failure, property, tripping, (===))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import PlutusCore (Name)
import PlutusCore.Annotation (SrcSpan (..))
import PlutusCore.Default
  ( DefaultBuiltinPattern (..)
  , DefaultFun
  , DefaultUni
  )
import PlutusCore.Error (ParserErrorBundle (ParseErrorB))
import PlutusCore.Flat (flat, unflat)
import PlutusCore.Generators.Hedgehog (forAllPretty)
import PlutusCore.Generators.Hedgehog.AST (runAstGen)
import PlutusCore.MkPlc (mkConstant)
import PlutusCore.Parser (defaultUni, parseGen)
import PlutusCore.Pretty (displayPlc)
import PlutusCore.Quote (runQuoteT)
import PlutusCore.Test (isSerialisable)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Golden (goldenVsString)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))
import Test.Tasty.Hedgehog (testPropertyNamed)
import Text.Megaparsec (errorBundlePretty)

import Data.ByteString.Lazy qualified as BSL
import Data.Text.Encoding (encodeUtf8)
import UntypedPlutusCore (Program)
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Core.Type (progTerm)
import UntypedPlutusCore.Generators.Hedgehog.AST (genProgram, regenConstantsUntil)
import UntypedPlutusCore.Parser (parseProgram, parseTerm)

--------------------------------------------------------------------------------
-- Main Test Group -------------------------------------------------------------

test_parsing :: TestTree
test_parsing =
  testGroup
    "Parsing"
    [ propFlat
    , propParser
    , propMatchParser
    , propTermSrcSpan
    , propUnit
    , propDefaultUni
    , testGroup
        "Error Messages"
        [ propListElementErrorLocation
        , propTypeNameTypoErrorLocation
        , propMissingClosingParen
        , propMissingClosingBracket
        , propMissingBuiltinOperand
        , propMissingConOperands
        , propInvalidKeyword
        , propBracketMismatch
        ]
    ]

--------------------------------------------------------------------------------
-- Test Definitions ------------------------------------------------------------

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
      :: T.Text
      -> Either
           ParserErrorBundle
           (Program Name DefaultUni DefaultFun DefaultBuiltinPattern SrcSpan)
    parseProg = runQuoteT . parseProgram

propMatchParser :: TestTree
propMatchParser =
  testGroup
    "Match classic parser"
    [ testCase "version 1.2 roundtrip" $ do
        let original = matchParserProgram $ UPLC.Version 1 2 0
            source = displayPlc original
        assertBool ("expected classic Match syntax in: " <> T.unpack source) $ "(match" `T.isInfixOf` source
        case runQuoteT $ parseProgram source of
          Left err -> assertFailure $ display err
          Right parsed -> void parsed @?= original
    , testCase "fixed-width pattern boundaries roundtrip" $ do
        let original = boundaryMatchParserProgram
        case runQuoteT . parseProgram $ displayPlc original of
          Left err -> assertFailure $ display err
          Right parsed -> void parsed @?= original
    , testCase "rejects Match before version 1.2" $ do
        let source = displayPlc . matchParserProgram $ UPLC.Version 1 1 0
        case runQuoteT $ parseProgram source of
          Left _ -> pure ()
          Right parsed -> assertFailure $ "parsed pre-1.2 Match program: " <> show parsed
    , testCase "rejects integer patterns outside the Int64 range" $ do
        assertMatchParseRejects $
          "(program 1.2.0 (match (con integer 0) "
            <> "(pattern (integer 9223372036854775808) (con integer 0))))"
        assertMatchParseRejects $
          "(program 1.2.0 (match (con integer 0) "
            <> "(pattern (integer -9223372036854775809) (con integer 0))))"
    , testCase "rejects Data.Constr pattern tags outside the Word64 range" $ do
        assertMatchParseRejects $
          "(program 1.2.0 (match (con integer 0) "
            <> "(pattern (data-constr -1) (con integer 0))))"
        assertMatchParseRejects $
          "(program 1.2.0 (match (con integer 0) "
            <> "(pattern (data-constr 18446744073709551616) (con integer 0))))"
    ]
  where
    assertMatchParseRejects source =
      case runQuoteT $ parseProgram source of
        Left _ -> pure ()
        Right parsed -> assertFailure $ "parsed out-of-range Match pattern: " <> show parsed

matchParserProgram
  :: UPLC.Version
  -> Program Name DefaultUni DefaultFun DefaultBuiltinPattern ()
matchParserProgram version =
  UPLC.Program
    ()
    version
    ( UPLC.Match
        ()
        (mkConstant @[Integer] () [1])
        ( Vector.fromList
            [
              ( DefaultPatternList $ Vector.singleton (DefaultPatternInteger 1)
              , mkConstant @Integer () 42
              )
            , (DefaultPatternWildcard, mkConstant @Integer () 0)
            ]
        )
    )

boundaryMatchParserProgram
  :: Program Name DefaultUni DefaultFun DefaultBuiltinPattern ()
boundaryMatchParserProgram =
  UPLC.Program
    ()
    (UPLC.Version 1 2 0)
    ( UPLC.Match
        ()
        (mkConstant @Integer () 0)
        ( Vector.fromList
            [ (DefaultPatternInteger minBound, mkConstant @Integer () 0)
            , (DefaultPatternInteger maxBound, mkConstant @Integer () 1)
            ,
              ( DefaultPatternDataConstr maxBound Vector.empty
              , mkConstant @Integer () 2
              )
            ]
        )
    )

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
      let sp = getAnn term
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
  testParseErrorGolden
    "List element error location"
    "list-element-type-mismatch"
    ( T.unlines
        [ "(program 1.1.0 "
        , "["
        , " (force (builtin mkCons)) (con integer 4) (con (list integer) [true]) ]"
        , ")"
        ]
    )

{-| Test that parser errors for typos in type names point to the correct location.
This tests the case where "boot" is used instead of "bool". -}
propTypeNameTypoErrorLocation :: TestTree
propTypeNameTypoErrorLocation =
  testParseErrorGolden
    "Type name typo error location"
    "type-name-typo"
    ( T.unlines
        [ "(program 1.1.0"
        , "[ (builtin integerToByteString) (con boot True) (con integer 0) (con integer 712372356934756347862573452345342345) ]"
        , ")"
        ]
    )

-- | Test that parser errors for missing closing parenthesis are clear.
propMissingClosingParen :: TestTree
propMissingClosingParen =
  testParseErrorGolden
    "Missing closing parenthesis error"
    "missing-closing-paren"
    "(program 1.1.0 (lam x (var x))"

-- | Test that parser errors for missing closing bracket are clear.
propMissingClosingBracket :: TestTree
propMissingClosingBracket =
  testParseErrorGolden
    "Missing closing bracket error"
    "missing-closing-bracket"
    "(program 1.1.0 [(builtin addInteger) (con integer 1) (con integer 2))"

-- | Test that parser errors for missing builtin operand are clear.
propMissingBuiltinOperand :: TestTree
propMissingBuiltinOperand =
  testParseErrorGolden
    "Missing builtin function name error"
    "missing-builtin-operand"
    "(program 1.1.0 (builtin))"

-- | Test that parser errors for missing con operands are clear.
propMissingConOperands :: TestTree
propMissingConOperands =
  testParseErrorGolden
    "Missing con operands error"
    "missing-con-operands"
    "(program 1.1.0 (con))"

-- | Test that parser errors for invalid keywords are clear.
propInvalidKeyword :: TestTree
propInvalidKeyword =
  testParseErrorGolden
    "Invalid keyword error"
    "invalid-keyword"
    "(program 1.1.0 (foo x))"

-- | Test that parser errors for bracket mismatches are clear.
propBracketMismatch :: TestTree
propBracketMismatch =
  testParseErrorGolden
    "Bracket type mismatch error"
    "bracket-mismatch"
    "(program 1.1.0 [(var x))"

--------------------------------------------------------------------------------
-- Helper Functions ------------------------------------------------------------

{-| Helper function to test parser error messages using golden files.
Verifies exact error message output against a golden file, ensuring error quality doesn't regress. -}
testParseErrorGolden :: String -> String -> T.Text -> TestTree
testParseErrorGolden testName goldenFileName code =
  goldenVsString
    testName
    ("untyped-plutus-core/test/Parser/Golden/" ++ goldenFileName ++ ".golden")
    $ case runQuoteT (parseProgram code) of
      Right _ -> error "Expected parse error, but parsing succeeded"
      Left (ParseErrorB errBundle) ->
        pure . BSL.fromStrict . encodeUtf8 . T.pack $ errorBundlePretty errBundle
