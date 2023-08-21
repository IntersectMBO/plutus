{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

-- | Tests for TPLC parser.
module Parser.Spec (tests) where

import PlutusCore
import PlutusCore.Error (ParserErrorBundle)
import PlutusCore.Generators.Hedgehog.AST
import PlutusPrelude

import Data.Text qualified as T
import Hedgehog hiding (Var)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty
import Test.Tasty.Hedgehog

-- | The `SrcSpan` of a parsed `Term` should not including trailing whitespaces.
propTermSrcSpan :: Property
propTermSrcSpan = property $ do
    term <- forAllWith display (runAstGen genTerm)
    let code = display (term :: Term TyName Name DefaultUni DefaultFun ())
    let (endingLine, endingCol) = length &&& T.length . last $ T.lines code
    trailingSpaces <- forAll $ Gen.text (Range.linear 0 10) (Gen.element [' ', '\n'])
    case runQuoteT . parseTerm @ParserErrorBundle $ code <> trailingSpaces of
        Right parsed ->
            let sp = termAnn parsed
             in (srcSpanELine sp, srcSpanECol sp) === (endingLine, endingCol + 1)
        Left err -> annotate (display err) >> failure

tests :: TestTree
tests =
    testGroup
        "parsing"
        [ testPropertyNamed
            "parser captures ending positions correctly"
            "propTermSrcSpan"
            propTermSrcSpan
        ]
