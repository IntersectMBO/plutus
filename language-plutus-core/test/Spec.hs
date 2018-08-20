{-# LANGUAGE OverloadedStrings #-}

module Main ( main
            ) where

import qualified Data.ByteString.Lazy    as BSL
import qualified Data.Text               as T
import           Data.Text.Encoding      (encodeUtf8)
import           Evaluation.Constant.All
import qualified Quotation.Spec as Quotation
import           Generators
import           Hedgehog                hiding (Var, annotate)
import           Language.PlutusCore
import           PlutusPrelude
import           Test.Tasty
import           Test.Tasty.Golden
import           Test.Tasty.Hedgehog
import           Test.Tasty.HUnit

main :: IO ()
main = do
    plcFiles <- findByExtension [".plc"] "test/data"
    rwFiles <- findByExtension [".plc"] "test/scopes"
    typeFiles <- findByExtension [".plc"] "test/types"
    defaultMain (allTests plcFiles rwFiles typeFiles)

compareName :: Name a -> Name a -> Bool
compareName = (==) `on` nameString

compareTyName :: TyName a -> TyName a -> Bool
compareTyName (TyName n) (TyName n') = compareName n n'

compareTerm :: Eq a => Term TyName Name a -> Term TyName Name a -> Bool
compareTerm (Var _ n) (Var _ n')                   = compareName n n'
compareTerm (TyAbs _ n k t) (TyAbs _ n' k' t')     = compareTyName n n' && k == k' && compareTerm t t'
compareTerm (LamAbs _ n ty t) (LamAbs _ n' ty' t') = compareName n n' && compareType ty ty' && compareTerm t t'
compareTerm (Apply _ t t'') (Apply _ t' t''')      = compareTerm t t' && compareTerm t'' t'''
compareTerm (Constant _ x) (Constant _ y)          = x == y
compareTerm (TyInst _ t ty) (TyInst _ t' ty')      = compareTerm t t' && compareType ty ty'
compareTerm (Unwrap _ t) (Unwrap _ t')             = compareTerm t t'
compareTerm (Wrap _ n ty t) (Wrap _ n' ty' t')     = compareTyName n n' && compareType ty ty' && compareTerm t t'
compareTerm (Error _ ty) (Error _ ty')             = compareType ty ty'
compareTerm _ _                                    = False

compareType :: Eq a => Type TyName a -> Type TyName a -> Bool
compareType (TyVar _ n) (TyVar _ n')                 = compareTyName n n'
compareType (TyFun _ t s) (TyFun _ t' s')            = compareType t t' && compareType s s'
compareType (TyFix _ n t) (TyFix _ n' t')            = compareTyName n n' && compareType t t'
compareType (TyForall _ n k t) (TyForall _ n' k' t') = compareTyName n n' && k == k' && compareType t t'
compareType (TyBuiltin _ x) (TyBuiltin _ y)          = x == y
compareType (TyLam _ n k t) (TyLam _ n' k' t')       = compareTyName n n' && k == k' && compareType t t'
compareType (TyApp _ t t') (TyApp _ t'' t''')        = compareType t t'' && compareType t' t'''
compareType (TyInt _ n) (TyInt _ n')                 = n == n'
compareType _ _                                      = False

compareProgram :: Eq a => Program TyName Name a -> Program TyName Name a -> Bool
compareProgram (Program _ v t) (Program _ v' t') = v == v' && compareTerm t t'

-- Generate a random 'Program', pretty-print it, and parse the pretty-printed
-- text, hopefully returning the same thing.
propParser :: Property
propParser = property $ do
    prog <- forAll genProgram
    let nullPosn = fmap (pure emptyPosn)
        reprint = BSL.fromStrict . encodeUtf8 . prettyText
        proc = nullPosn <$> parse (reprint prog)
        compared = and (compareProgram (nullPosn prog) <$> proc)
    Hedgehog.assert compared

allTests :: [FilePath] -> [FilePath] -> [FilePath] -> TestTree
allTests plcFiles rwFiles typeFiles = testGroup "all tests"
    [ tests
    , testProperty "parser round-trip" propParser
    , testsGolden plcFiles
    , testsRewrite rwFiles
    , testsType typeFiles
    , test_constantApplication
    , Quotation.tests
    ]

type TestFunction a = BSL.ByteString -> Either a T.Text

asIO :: Pretty a => TestFunction a -> FilePath -> IO BSL.ByteString
asIO f = fmap (either errorgen (BSL.fromStrict . encodeUtf8) . f) . BSL.readFile

errorgen :: Pretty a => a -> BSL.ByteString
errorgen = BSL.fromStrict . encodeUtf8 . prettyText

asGolden :: Pretty a => TestFunction a -> TestName -> TestTree
asGolden f file = goldenVsString file (file ++ ".golden") (asIO f file)

testsType :: [FilePath] -> TestTree
testsType = testGroup "golden type synthesis tests" . fmap (asGolden printType)

testsGolden :: [FilePath] -> TestTree
testsGolden = testGroup "golden tests" . fmap (asGolden (format defaultCfg))

testsRewrite :: [FilePath] -> TestTree
testsRewrite = testGroup "golden rewrite tests" . fmap (asGolden (format debugCfg))

tests :: TestTree
tests = testCase "example programs" $ fold
    [ format cfg "(program 0.1.0 [(con addInteger) x y])" @?= Right "(program 0.1.0 [ [ (con addInteger) x ] y ])"
    , format cfg "(program 0.1.0 doesn't)" @?= Right "(program 0.1.0 doesn't)"
    , format cfg "{- program " @?= Left (LexErr "Error in nested comment at line 1, column 12")
    ]
    where cfg = defaultCfg
