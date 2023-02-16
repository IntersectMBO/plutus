-- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Tests for PIR parser.
module ParserSpec (parsing) where

import PlutusPrelude

import Data.Char
import Data.Text qualified as T

import PlutusCore (runQuoteT)
import PlutusCore.Annotation
import PlutusCore.Default qualified as PLC
import PlutusCore.Error (ParserErrorBundle)
import PlutusIR
import PlutusIR.Generators.AST
import PlutusIR.Parser

import Hedgehog hiding (Var)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range

import Test.Tasty
import Test.Tasty.Extras
import Test.Tasty.Hedgehog

newtype PrettyProg = PrettyProg { prog :: Program TyName Name PLC.DefaultUni PLC.DefaultFun SrcSpan }
instance Show PrettyProg where
    show = display . prog

whitespace :: MonadGen m => m String
whitespace = flip replicate ' ' <$> Gen.integral (Range.linear 1 4)

lineComment :: MonadGen m => m String
lineComment = (Gen.string (Range.linear 0 20) $ Gen.filterT (/= '\n') Gen.latin1)
              >>= (\s -> return $ " --" ++ s ++ "\n")

blockComment :: MonadGen m => m String
blockComment = (Gen.string (Range.linear 0 20) $ Gen.element notBraces)
               >>= (\s -> return $ "{- " ++ s ++ " -}")
    where notBraces :: String
          notBraces = filter (\c -> c /= '{' && c /= '}') ['\0' .. '\255']

comment :: MonadGen m => m String
comment = Gen.choice [Gen.constant "", lineComment, blockComment]

separators :: String
separators = ['!', '(', ')', '[', ']', '{', '}']

separator :: Char -> Bool
separator c = c `elem` separators || isSpace c

aroundSeparators :: MonadGen m => m String -> String -> m String
aroundSeparators _ [] = return []
aroundSeparators splice [s] = (s:) <$> splice
aroundSeparators splice (a:b:l)
    | separator b = do
          s1 <- splice
          s2 <- splice
          rest <- aroundSeparators splice l
          return $ a : s1 ++ b : s2 ++ rest
    | otherwise = (a :) <$> aroundSeparators splice (b:l)

genScrambledWith :: MonadGen m => m String -> m (String, String)
genScrambledWith splice = do
    original <- display <$> runAstGen genProgram
    scrambled <- aroundSeparators splice original
    return (original, scrambled)

propRoundTrip :: Property
propRoundTrip = property $ do
    code <- display <$> forAllWith display (runAstGen genProgram)
    let backward = fmap (display . prog)
        forward = fmap PrettyProg . parseProg
    tripping code forward backward

-- | The `SrcSpan` of a parsed `Term` should not including trailing whitespaces.
propTermSrcSpan :: Property
propTermSrcSpan = property $ do
    code <- display <$> forAllWith display (runAstGen genTerm)
    let (endingLine, endingCol) = length &&& T.length . last $ T.lines code
    trailingSpaces <- forAll $ Gen.text (Range.linear 0 10) (Gen.element [' ', '\n'])
    case parseTerm (code <> trailingSpaces) of
        Right term ->
            let sp = termAnn term
             in (srcSpanELine sp, srcSpanECol sp) === (endingLine, endingCol + 1)
        Left err -> annotate (display err) >> failure

parseProg ::
    T.Text ->
    Either
        ParserErrorBundle
        (Program TyName Name PLC.DefaultUni PLC.DefaultFun SrcSpan)
parseProg p =
    runQuoteT $ parse program "test" p

parseTerm ::
    T.Text ->
    Either
        ParserErrorBundle
        (Term TyName Name PLC.DefaultUni PLC.DefaultFun SrcSpan)
parseTerm p =
    runQuoteT $ parse pTerm "test" p

propIgnores :: Gen String -> Property
propIgnores splice = property $ do
    (original, scrambled) <- forAll (genScrambledWith splice)
    let displayProgram :: Program TyName Name PLC.DefaultUni PLC.DefaultFun SrcSpan -> String
        displayProgram = display
        parse1 = displayProgram <$> (parseProg $ T.pack original)
        parse2 = displayProgram <$> (parseProg $ T.pack scrambled)
    parse1 === parse2

parsing :: TestNested
parsing = return $ testGroup "parsing"
    [ testPropertyNamed "parser round-trip" "propRoundTrip" propRoundTrip
    , testPropertyNamed "parser ignores whitespace" "propIgnores whitespace" (propIgnores whitespace)
    , testPropertyNamed "parser ignores comments" "propIgnores comments" (propIgnores comment)
    , testPropertyNamed "parser captures ending positions correctly" "propTermSrcSpan" propTermSrcSpan
    ]
