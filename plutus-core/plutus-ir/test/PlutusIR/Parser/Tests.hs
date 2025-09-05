-- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds         #-}

-- | Tests for PIR parser.
module PlutusIR.Parser.Tests where

import PlutusPrelude

import PlutusCore qualified as PLC
import PlutusCore.Annotation
import PlutusCore.Default (noMoreTypeFunctions)
import PlutusCore.Error (ParserErrorBundle)
import PlutusCore.Test (isSerialisable, mapTestLimitAtLeast)
import PlutusIR
import PlutusIR.Generators.AST
import PlutusIR.Parser

import Data.Char
import Data.Text qualified as T
import Hedgehog hiding (Var)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty
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
aroundSeparators = go False False
  where
    -- Quoted names may contain separators, but they are part of the name, so
    -- we cannot scramble inside quoted names.
    go inQuotedName inUnique splice = \case
        [] -> pure []
        [s] -> (s:) <$> splice
        ('`' : '-' : l) | inQuotedName -> do
          let (digits, notDigits) = break isDigit l
          rest <- go (not inQuotedName) True splice notDigits
          pure $ "`-" ++ digits ++ rest
        ('`' : l) -> do
            s <- splice
            rest <- go (not inQuotedName) inUnique splice l
            pure $ if inQuotedName
              then '`' : s ++ rest
              else s ++ '`' : rest
        (a : b : l)
            | not inQuotedName && separator b -> do
                s1 <- splice
                s2 <- splice
                rest <- go inQuotedName inUnique splice l
                pure $ a : s1 ++ b : s2 ++ rest
            | otherwise -> (a :) <$> go inQuotedName inUnique splice (b : l)

-- | Check whether the given constant can be scrambled (in the sense of 'genScrambledWith').
isScramblable :: PLC.Some (PLC.ValueOf PLC.DefaultUni) -> Bool
isScramblable (PLC.Some (PLC.ValueOf uni0 x0)) = go uni0 x0 where
    go :: PLC.DefaultUni (PLC.Esc a) -> a -> Bool
    go PLC.DefaultUniInteger _ = True
    go PLC.DefaultUniByteString _ = True
    -- Keep in sync with 'aroundSeparators'.
    go PLC.DefaultUniString text = T.all (\c -> not (separator c) && c /= '`') text
    go PLC.DefaultUniUnit _ = True
    go PLC.DefaultUniBool _ = True
    go (PLC.DefaultUniProtoList `PLC.DefaultUniApply` uniA) xs = all (go uniA) xs
    go (PLC.DefaultUniProtoArray `PLC.DefaultUniApply` uniA) xs = all (go uniA) xs
    go (PLC.DefaultUniProtoPair `PLC.DefaultUniApply` uniA `PLC.DefaultUniApply` uniB) (x, y) =
        go uniA x && go uniB y
    go (f `PLC.DefaultUniApply` _ `PLC.DefaultUniApply` _ `PLC.DefaultUniApply` _) _  =
        noMoreTypeFunctions f
    go PLC.DefaultUniData _ = True
    go PLC.DefaultUniValue _ = True
    go PLC.DefaultUniBLS12_381_G1_Element _ = False
    go PLC.DefaultUniBLS12_381_G2_Element _ = False
    go PLC.DefaultUniBLS12_381_MlResult _ = False

genScrambledWith :: MonadGen m => m String -> m (String, String)
genScrambledWith splice = do
    original <- display <$> runAstGen (regenConstantsUntil isScramblable =<< genProgram)
    scrambled <- aroundSeparators splice original
    return (original, scrambled)

propRoundTrip :: Property
propRoundTrip = property $ do
    code <- display <$>
        forAllWith display (runAstGen $ regenConstantsUntil isSerialisable =<< genProgram)
    let backward = fmap (display . prog)
        forward = fmap PrettyProg . parseProg
    tripping code forward backward

-- | The `SrcSpan` of a parsed `Term` should not including trailing whitespaces.
propTermSrcSpan :: Property
propTermSrcSpan = property $ do
    code <- display . _progTerm <$>
        forAllWith display (runAstGen $ regenConstantsUntil isSerialisable =<< genProgram)
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
    PLC.runQuoteT $ parse program "test" p

parseTerm ::
    T.Text ->
    Either
        ParserErrorBundle
        (Term TyName Name PLC.DefaultUni PLC.DefaultFun SrcSpan)
parseTerm p =
    PLC.runQuoteT $ parse pTerm "test" p

propIgnores :: Gen String -> Property
propIgnores splice = property $ do
    (original, scrambled) <- forAll (genScrambledWith splice)
    let displayProgram :: Program TyName Name PLC.DefaultUni PLC.DefaultFun SrcSpan -> String
        displayProgram = display
        parse1 = displayProgram <$> parseProg (T.pack original)
        parse2 = displayProgram <$> parseProg (T.pack scrambled)
    parse1 === parse2

test_parsing :: TestTree
test_parsing = testGroup "parsing"
    [ testPropertyNamed
        "parser round-trip"
        "propRoundTrip"
        (mapTestLimitAtLeast 99 (`div` 2) $ propRoundTrip)
    , testPropertyNamed
        "parser ignores whitespace"
        "propIgnores whitespace"
        (mapTestLimitAtLeast 50 (`div` 8) $ propIgnores whitespace)
    , testPropertyNamed
        "parser ignores comments"
        "propIgnores comments"
        (mapTestLimitAtLeast 30 (`div` 30) $ propIgnores comment)
    , testPropertyNamed
        "parser captures ending positions correctly"
        "propTermSrcSpan"
        (mapTestLimitAtLeast 99 (`div` 2) $ propTermSrcSpan)
    ]
