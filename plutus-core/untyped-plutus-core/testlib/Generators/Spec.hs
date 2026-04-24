-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

-- | UPLC property tests (pretty-printing\/parsing and binary encoding\/decoding).
module Generators.Spec where

import PlutusPrelude (display, fold, void, (&&&))

import Control.Lens (view)
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
import Test.Tasty.Golden (goldenVsString)
import Test.Tasty.HUnit (testCase, (@?=))
import Test.Tasty.Hedgehog (testPropertyNamed)
import Text.Megaparsec (errorBundlePretty)

import Data.ByteString.Lazy qualified as BSL
import Data.Text.Encoding (encodeUtf8)
import UntypedPlutusCore (Program)
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Core.Type (progTerm, termAnn)
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
        , propInvalidIdentifierHyphenLetters
        , propInvalidIdentifierHyphenWord
        , propInvalidIdentifierDoubleUnique
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

{- Note [Negative identifier-grammar tests]
The parser's name grammar treats '-NNN' purely as the numeric unique-suffix:
'foo-123' → Name "foo" (Unique 123). A '-' anywhere else in an identifier is
not allowed by the unquoted grammar (see 'isIdentifierChar' in
'PlutusCore.Name.Unique'). Several tools in the wild (e.g. Scalus 0.16.0's
'toUplcOptimized') emit names like 'pubKeyHash-305478r71' that violate this,
and today the parser mis-parses them in a way that surfaces as a confusing
error hundreds of lines away from the offending name — see issue #7742.

The goldens below freeze the *current* (unhelpful) error output so that a
future diagnostic improvement shows up as an explicit golden-file diff.
When the parser is taught to point at the bad name itself, accept the new
goldens with 'scripts/regen-goldens.sh' (or '--accept'). -}

{-| @pubKeyHash-305478r71@ — the exact shape Scalus 0.16.0 produces, inside a
binder. Current behaviour: the parser eats @pubKeyHash-305478@ as name+unique,
picks up @r71@ as the lam body, then fails far away on the next paren. -}
propInvalidIdentifierHyphenLetters :: TestTree
propInvalidIdentifierHyphenLetters =
  testParseErrorGolden
    "Invalid identifier: hyphen followed by digits then letters"
    "invalid-identifier-hyphen-letters"
    "(program 1.1.0 (lam pubKeyHash-305478r71 (lam x x)))"

{-| @foo-bar@ — hyphen followed by non-digits. Current behaviour: the parser
stops at '-' (it is not in 'isIdentifierChar'), takes @foo@ as the name, and
then explodes on @-bar@ which is not a valid continuation anywhere. -}
propInvalidIdentifierHyphenWord :: TestTree
propInvalidIdentifierHyphenWord =
  testParseErrorGolden
    "Invalid identifier: hyphen followed by non-digits"
    "invalid-identifier-hyphen-word"
    "(program 1.1.0 (lam foo-bar foo-bar))"

{-| @foo-123-456@ — ambiguous double '-NNN' run. Current behaviour: the first
@-123@ wins as the unique, @-456@ is left over and fails the next check. -}
propInvalidIdentifierDoubleUnique :: TestTree
propInvalidIdentifierDoubleUnique =
  testParseErrorGolden
    "Invalid identifier: double unique-suffix"
    "invalid-identifier-double-unique"
    "(program 1.1.0 (lam foo-123-456 foo-123-456))"

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
