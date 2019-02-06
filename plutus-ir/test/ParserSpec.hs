{-# LANGUAGE FlexibleContexts #-}
module ParserSpec (parsing) where

import           PlutusPrelude

import           Common

import           Data.Char

import           Language.PlutusIR
import           Language.PlutusIR.Generators.AST
import           Language.PlutusIR.Parser         hiding (whitespace)

import           Hedgehog                         hiding (Var)
import qualified Hedgehog.Gen                     as Gen
import qualified Hedgehog.Range                   as Range

import           Text.Megaparsec                  hiding (failure, parse)

import           Test.Tasty
import           Test.Tasty.Hedgehog

newtype PrettyProg = PrettyProg { prog :: Program TyName Name SourcePos }
instance Show PrettyProg where
    show = prettyString . prog

whitespace :: MonadGen m => m String
whitespace = flip replicate ' ' <$> Gen.integral (Range.linear 1 4)

lineComment :: MonadGen m => m String
lineComment = Gen.filter (not . ('\n' `elem`)) (Gen.string (Range.linear 0 100) Gen.latin1)
              >>= (\s -> return $ " --" ++ s ++ "\n")

blockComment :: MonadGen m => m String
blockComment = Gen.filter (not . hasBlockComments) (Gen.string (Range.linear 0 100) Gen.latin1)
               >>= (\s -> return $ "{- " ++ s ++ " -}")
    where hasBlockComments []          = False
          hasBlockComments [_]         = False
          hasBlockComments ('{':'-':_) = True
          hasBlockComments ('-':'}':_) = True
          hasBlockComments (_:c:r)     = hasBlockComments (c:r)

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
    original <- prettyString <$> genProgram
    scrambled <- aroundSeparators splice original
    return (original, scrambled)

propRoundTrip :: Property
propRoundTrip = property $ do
    code <- prettyString <$> forAllWith prettyString genProgram
    let backward = fmap show
        forward = fmap PrettyProg . parse program "test"
    tripping code forward backward

propIgnores :: Gen String -> Property
propIgnores splice = property $ do
    (original, scrambled) <- forAll (genScrambledWith splice)
    (prettyString <$> parse program "test" original) === (prettyString <$> parse program "test" scrambled)

parsing :: TestNested
parsing = return $ testGroup "parsing"
    [ testProperty "parser round-trip" propRoundTrip
    , testProperty "parser ignores whitespace" (propIgnores whitespace)
    , testProperty "parser ignores comments" (propIgnores comment)
    ]
