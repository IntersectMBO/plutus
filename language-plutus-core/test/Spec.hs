{-# LANGUAGE OverloadedStrings #-}

module Main ( main
            ) where

import qualified Data.ByteString.Lazy as BSL
import qualified Data.Text            as T
import           Data.Text.Encoding   (encodeUtf8)
import           Hedgehog             hiding (Size, Var, annotate)
import qualified Hedgehog.Gen         as Gen
import qualified Hedgehog.Range       as Range
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
compareTerm (Apply _ t t') (Apply _ t'' t''')      = compareTerm t t'' && compareTerm t' t'''
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

genVersion :: MonadGen m => m (Version AlexPosn)
genVersion = Version emptyPosn <$> int' <*> int' <*> int'
    where int' = Gen.integral_ (Range.linear 0 10)

genTyName :: MonadGen m => m (TyName AlexPosn)
genTyName = TyName <$> genName

-- TODO make this robust against generating identfiers such as "fix"?
genName :: MonadGen m => m (Name AlexPosn)
genName = Name emptyPosn <$> name' <*> int'
    where int' = Unique <$> Gen.int (Range.linear 0 3000)
          name' = BSL.fromStrict <$> Gen.utf8 (Range.linear 1 20) Gen.lower

simpleRecursive :: MonadGen m => [m a] -> [m a] -> m a
simpleRecursive = Gen.recursive Gen.choice

genKind :: MonadGen m => m (Kind AlexPosn)
genKind = simpleRecursive nonRecursive recursive
    where nonRecursive = pure <$> sequence [Type, Size] emptyPosn
          recursive = [KindArrow emptyPosn <$> genKind <*> genKind]

genBuiltinName :: MonadGen m => m BuiltinName
genBuiltinName = Gen.choice $ pure <$>
    [ AddInteger, SubtractInteger, MultiplyInteger, DivideInteger, RemainderInteger
    , LessThanInteger, LessThanEqInteger, GreaterThanInteger, GreaterThanEqInteger
    , EqInteger, ResizeInteger, IntToByteString, Concatenate, TakeByteString
    , DropByteString, ResizeByteString, SHA2, SHA3, VerifySignature
    , EqByteString, TxHash, BlockNum, BlockTime
    ]

genBuiltin :: MonadGen m => m (Constant AlexPosn)
genBuiltin = Gen.choice [BuiltinName emptyPosn <$> genBuiltinName, genInt, genSize, genBS]
    where int' = Gen.integral_ (Range.linear (-10000000) 10000000)
          size' = Gen.integral_ (Range.linear 1 10)
          string' = BSL.fromStrict <$> Gen.utf8 (Range.linear 0 40) Gen.unicode
          genInt = BuiltinInt emptyPosn <$> size' <*> int'
          genSize = BuiltinSize emptyPosn <$> size'
          genBS = BuiltinBS emptyPosn <$> size' <*> string'

genType :: MonadGen m => m (Type TyName AlexPosn)
genType = simpleRecursive nonRecursive recursive
    where varGen = TyVar emptyPosn <$> genTyName
          funGen = TyFun emptyPosn <$> genType <*> genType
          lamGen = TyLam emptyPosn <$> genTyName <*> genKind <*> genType
          forallGen = TyForall emptyPosn <$> genTyName <*> genKind <*> genType
          applyGen = TyApp emptyPosn <$> genType <*> genType
          numGen = TyInt emptyPosn <$> Gen.integral (Range.linear 0 256)
          recursive = [funGen, applyGen]
          nonRecursive = [varGen, lamGen, forallGen, numGen]

genTerm :: MonadGen m => m (Term TyName Name AlexPosn)
genTerm = simpleRecursive nonRecursive recursive
    where varGen = Var emptyPosn <$> genName
          absGen = TyAbs emptyPosn <$> genTyName <*> genKind <*> genTerm
          instGen = TyInst emptyPosn <$> genTerm <*> genType
          lamGen = LamAbs emptyPosn <$> genName <*> genType <*> genTerm
          applyGen = Apply emptyPosn <$> genTerm <*> genTerm
          unwrapGen = Unwrap emptyPosn <$> genTerm
          wrapGen = Wrap emptyPosn <$> genTyName <*> genType <*> genTerm
          errorGen = Error emptyPosn <$> genType
          recursive = [absGen, instGen, lamGen, applyGen, unwrapGen, wrapGen]
          nonRecursive = [varGen, Constant emptyPosn <$> genBuiltin, errorGen]

genProgram :: MonadGen m => m (Program TyName Name AlexPosn)
genProgram = Program emptyPosn <$> genVersion <*> genTerm

emptyPosn :: AlexPosn
emptyPosn = AlexPn 0 0 0

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
    ]

type TestFunction a = BSL.ByteString -> Either a T.Text

asIO :: Pretty a => TestFunction a -> FilePath -> IO BSL.ByteString
asIO f = fmap (either errorgen (BSL.fromStrict . encodeUtf8) . f) . BSL.readFile

errorgen :: Pretty a => a -> BSL.ByteString
errorgen = BSL.fromStrict . encodeUtf8 . prettyText

withTypes :: BSL.ByteString -> Either Error T.Text
withTypes = collectErrors . fmap (fmap showType . annotateST) . parseScoped

showType :: Pretty a => (TypeState a, Program TyNameWithKind NameWithType a) -> T.Text
showType = uncurry (either prettyText prettyText .* programType 10000)

asGolden :: Pretty a => TestFunction a -> TestName -> TestTree
asGolden f file = goldenVsString file (file ++ ".golden") (asIO f file)

testsType :: [FilePath] -> TestTree
testsType = testGroup "golden type synthesis tests" . fmap (asGolden withTypes)

testsGolden :: [FilePath] -> TestTree
testsGolden = testGroup "golden tests" . fmap (asGolden format)

testsRewrite :: [FilePath] -> TestTree
testsRewrite = testGroup "golden rewrite tests" . fmap (asGolden debugScopes)

tests :: TestTree
tests = testCase "example programs" $ fold
    [ format "(program 0.1.0 [(con addInteger) x y])" @?= Right "(program 0.1.0 [ [ (con addInteger) x ] y ])"
    , format "(program 0.1.0 doesn't)" @?= Right "(program 0.1.0 doesn't)"
    , format "{- program " @?= Left (LexErr "Error in nested comment at line 1, column 12")
    ]
