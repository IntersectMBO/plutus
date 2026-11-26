-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

-- | UPLC property tests (pretty-printing\/parsing and binary encoding\/decoding).
module Generators.Spec where

import PlutusPrelude (display, fold, getAnn, void, (&&&))

import Control.Lens (view)
import Data.Foldable qualified as F
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Hedgehog (Gen, annotate, annotateShow, failure, forAll, property, tripping, (===))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import PlutusCore (Name (..), Unique (..))
import PlutusCore.Annotation (SrcSpan (..))
import PlutusCore.Default (DefaultFun, DefaultUni)
import PlutusCore.Error (ParserError (..), ParserErrorBundle (ParseErrorB))
import PlutusCore.Flat (flat, unflat)
import PlutusCore.Generators.Hedgehog (forAllPretty)
import PlutusCore.Generators.Hedgehog.AST (runAstGen)
import PlutusCore.Parser (defaultUni, parseGen)
import PlutusCore.Pretty (displayPlc)
import PlutusCore.Quote (runQuoteT)
import PlutusCore.Test (isSerialisable)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Golden (goldenVsString)
import Test.Tasty.HUnit (testCase, (@?=))
import Test.Tasty.Hedgehog (testPropertyNamed)
import Text.Megaparsec (ErrorFancy (..), ParseError (..), bundleErrors, errorBundlePretty)

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
        , propValidUniqueSuffix
        , propInvalidUniqueSuffix
        , propInvalidUniqueSuffixScalusRegression
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

propInvalidUniqueSuffixScalusRegression :: TestTree
propInvalidUniqueSuffixScalusRegression =
  testParseErrorGolden
    "MalformedUniqueSuffix: Scalus pubKeyHash-305478r71 regression (#7742)"
    "malformed-unique-suffix-scalus"
    "(program 1.1.0 (lam pubKeyHash-305478r71 (lam x x)))"

{-| A '<base>-<digits>' unquoted name parses to a 'Name' carrying the base
text and a 'Unique' equal to the digits. -}
propValidUniqueSuffix :: TestTree
propValidUniqueSuffix =
  testPropertyNamed
    "Valid unique suffix: <base>-<digits> parses to Name <base> (Unique <digits>)"
    "valid-unique-suffix"
    $ property
    $ do
      base <- forAll genBaseName
      n <- forAll (Gen.integral (Range.linear 0 9999999))
      let nText = T.pack (show (n :: Int))
          input = "(lam " <> base <> "-" <> nText <> " (con bool True))"
      case runQuoteT (parseTerm input) of
        Right (UPLC.LamAbs _ binder _) -> do
          _nameText binder === base
          _nameUnique binder === Unique n
        Right other -> do
          annotate ("Expected LamAbs, got: " <> show other)
          failure
        Left bundle -> do
          annotateShow bundle
          failure

{-| A '<base>-<bad>' unquoted name (where '<bad>' is empty, contains a
non-digit, or contains another '-') raises 'MalformedUniqueSuffix' carrying
'<base>' and '<bad>' verbatim. -}
propInvalidUniqueSuffix :: TestTree
propInvalidUniqueSuffix =
  testPropertyNamed
    "Invalid unique suffix: <base>-<bad> raises MalformedUniqueSuffix <base> <bad>"
    "invalid-unique-suffix"
    $ property
    $ do
      base <- forAll genBaseName
      bad <- forAll genBadSuffix
      let input = "(lam " <> base <> "-" <> bad <> " (con bool True))"
      case runQuoteT (parseTerm input) of
        Right ok -> do
          annotate ("Expected MalformedUniqueSuffix, got success: " <> show ok)
          failure
        Left bundle ->
          case extractMalformedUniqueSuffix bundle of
            Just (b, s) -> do
              b === base
              s === bad
            Nothing -> do
              annotateShow bundle
              failure
  where
    extractMalformedUniqueSuffix :: ParserErrorBundle -> Maybe (Text, Text)
    extractMalformedUniqueSuffix (ParseErrorB bundle) =
      case [ (b, s)
           | err <- F.toList (bundleErrors bundle)
           , (b, s) <- fanciesOf err
           ] of
        (x : _) -> Just x
        [] -> Nothing
    fanciesOf (FancyError _ es) =
      [(b, s) | ErrorCustom (MalformedUniqueSuffix b s _) <- Set.toList es]
    fanciesOf _ = []

-- Generators for unquoted-name property tests.

genIdStartChar :: Gen Char
genIdStartChar =
  Gen.choice [Gen.element ['a' .. 'z'], Gen.element ['A' .. 'Z'], pure '_']

genIdRestChar :: Gen Char
genIdRestChar =
  Gen.choice [genIdStartChar, Gen.element ['0' .. '9'], pure '\'']

genBaseName :: Gen Text
genBaseName = do
  hd <- genIdStartChar
  tl <- Gen.list (Range.linear 0 8) genIdRestChar
  pure (T.pack (hd : tl))

{-| Generate a guaranteed-malformed suffix by either returning the empty string,
or starting from a valid digit-string base (possibly empty) and inserting one
or more invalidating characters at random positions. The invalidating set is
'isNameExtensionChar' minus digits, so any single insertion turns the result
into a non-digit-only string. -}
genBadSuffix :: Gen Text
genBadSuffix =
  Gen.choice
    [ pure T.empty
    , do
        base <- T.pack <$> Gen.list (Range.linear 0 8) (Gen.element ['0' .. '9'])
        n <- Gen.integral (Range.linear 1 3 :: Range.Range Int)
        applyMutations n base
    ]
  where
    applyMutations :: Int -> Text -> Gen Text
    applyMutations 0 t = pure t
    applyMutations k t = insertInvalidatingChar t >>= applyMutations (k - 1)

    insertInvalidatingChar :: Text -> Gen Text
    insertInvalidatingChar t = do
      pos <- Gen.integral (Range.linear 0 (T.length t))
      c <- Gen.element invalidatingChars
      pure (T.take pos t <> T.singleton c <> T.drop pos t)

    invalidatingChars :: String
    invalidatingChars = ['a' .. 'z'] <> ['A' .. 'Z'] <> "_'-"

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
