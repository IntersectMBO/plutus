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
import PlutusCore.Error (ParserErrorBundle)
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
    code <-
      display
        <$> forAllPretty
          ( view progTerm
              <$> runAstGen (regenConstantsUntil isSerialisable =<< genProgram @DefaultFun)
          )
    annotateShow code
    let (endingLine, endingCol) = length &&& T.length . last $ T.lines code
    trailingSpaces <- forAllPretty $ Gen.text (Range.linear 0 10) (Gen.element [' ', '\n'])
    case runQuoteT . parseTerm $ code <> trailingSpaces of
      Right parsed ->
        let sp = termAnn parsed
         in (srcSpanELine sp, srcSpanECol sp) === (endingLine, endingCol + 1)
      Left err -> annotate (display err) >> failure

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

test_parsing :: TestTree
test_parsing =
  testGroup
    "Parsing"
    [ propFlat
    , propParser
    , propTermSrcSpan
    , propUnit
    , propDefaultUni
    ]
