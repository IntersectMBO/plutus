{-# LANGUAGE OverloadedStrings #-}

module Main ( main
            ) where

import qualified Check.Spec                                 as Check
import           Codec.Serialise
import           Control.Monad.Except
import           Control.Monad.Morph
import qualified Data.ByteString.Lazy                       as BSL
import qualified Data.Text                                  as T
import           Data.Text.Encoding                         (encodeUtf8)
import           Evaluation.CkMachine
import           Evaluation.Constant.All
import           Generators
import           Hedgehog                                   hiding (Var)
import qualified Hedgehog.Gen                               as Gen
import qualified Hedgehog.Range                             as Range
import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.DeBruijn
import           Language.PlutusCore.Generators
import           Language.PlutusCore.Generators.Interesting
import           Language.PlutusCore.Pretty
import           Normalization.Type
import           PlutusPrelude                              hiding (hoist)
import           Pretty.Readable
import qualified Quotation.Spec                             as Quotation
import           Test.Tasty
import           Test.Tasty.Golden
import           Test.Tasty.Hedgehog
import           Test.Tasty.HUnit
import           TypeSynthesis.Spec                         (test_typecheck)

main :: IO ()
main = do
    plcFiles <- findByExtension [".plc"] "test/data"
    rwFiles <- findByExtension [".plc"] "test/scopes"
    typeFiles <- findByExtension [".plc"] "test/types"
    typeNormalizeFiles <- findByExtension [".plc"] "test/normalize-types"
    typeErrorFiles <- findByExtension [".plc"] "test/type-errors"
    defaultMain (allTests plcFiles rwFiles typeFiles typeNormalizeFiles typeErrorFiles)

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
compareTerm (Builtin _ bi) (Builtin _ bi')         = bi == bi'
compareTerm (TyInst _ t ty) (TyInst _ t' ty')      = compareTerm t t' && compareType ty ty'
compareTerm (Unwrap _ t) (Unwrap _ t')             = compareTerm t t'
compareTerm (IWrap _ pat1 arg1 t1) (IWrap _ pat2 arg2 t2) =
    compareType pat1 pat2 && compareType arg1 arg2 && compareTerm t1 t2
compareTerm (Error _ ty) (Error _ ty')             = compareType ty ty'
compareTerm _ _                                    = False

compareType :: Eq a => Type TyName a -> Type TyName a -> Bool
compareType (TyVar _ n) (TyVar _ n')                  = compareTyName n n'
compareType (TyFun _ t s) (TyFun _ t' s')             = compareType t t' && compareType s s'
compareType (TyIFix _ pat1 arg1) (TyIFix _ pat2 arg2) = compareType pat1 pat2 && compareType arg1 arg2
compareType (TyForall _ n k t) (TyForall _ n' k' t')  = compareTyName n n' && k == k' && compareType t t'
compareType (TyBuiltin _ x) (TyBuiltin _ y)           = x == y
compareType (TyLam _ n k t) (TyLam _ n' k' t')        = compareTyName n n' && k == k' && compareType t t'
compareType (TyApp _ t t') (TyApp _ t'' t''')         = compareType t t'' && compareType t' t'''
compareType (TyInt _ n) (TyInt _ n')                  = n == n'
compareType _ _                                       = False

compareProgram :: Eq a => Program TyName Name a -> Program TyName Name a -> Bool
compareProgram (Program _ v t) (Program _ v' t') = v == v' && compareTerm t t'

-- | A 'Program' which we compare using textual equality of names rather than alpha-equivalence.
newtype TextualProgram a = TextualProgram { unTextualProgram :: Program TyName Name a } deriving Show

instance Eq a => Eq (TextualProgram a) where
    (TextualProgram p1) == (TextualProgram p2) = compareProgram p1 p2

propCBOR :: Property
propCBOR = property $ do
    prog <- forAll genProgram
    Hedgehog.tripping prog serialise deserialiseOrFail

-- Generate a random 'Program', pretty-print it, and parse the pretty-printed
-- text, hopefully returning the same thing.
propParser :: Property
propParser = property $ do
    prog <- TextualProgram . void <$> forAll genProgram
    let reprint = BSL.fromStrict . encodeUtf8 . prettyPlcDefText . unTextualProgram
    Hedgehog.tripping prog reprint (fmap (TextualProgram . void) . parse)

propRename :: Property
propRename = property $ do
    prog <- forAll genProgram
    Hedgehog.assert $ runQuote (rename prog) == prog

propDeBruijn :: GenT Quote (TermOf (TypedBuiltinValue size a)) -> Property
propDeBruijn gen = property . hoist (return . runQuote) $ do
    (TermOf body _) <- forAllNoShowT gen
    let
        forward = deBruijnTerm
        backward :: Except FreeVariableError (Term TyDeBruijn DeBruijn a) -> Except FreeVariableError (Term TyName Name a)
        backward e = e >>= (\t -> runQuoteT $ unDeBruijnTerm t)
    Hedgehog.tripping body forward backward

allTests :: [FilePath] -> [FilePath] -> [FilePath] -> [FilePath] -> [FilePath] -> TestTree
allTests plcFiles rwFiles typeFiles typeNormalizeFiles typeErrorFiles = testGroup "all tests"
    [ tests
    , testsSizeOfInteger
    , testProperty "parser round-trip" propParser
    , testProperty "serialization round-trip" propCBOR
    , testProperty "equality survives renaming" propRename
    , testGroup "de Bruijn transformation round-trip" (fromInterestingTermGens (\name gen -> testProperty name (propDeBruijn gen)))
    , testsGolden plcFiles
    , testsRewrite rwFiles
    , testsType typeFiles
    , testsNormalizeType typeNormalizeFiles
    , testsType typeErrorFiles
    , test_Pretty
    , test_typeNormalization
    , test_typecheck
    , test_constant
    , test_evaluateCk
    , Quotation.tests
    , Check.tests
    ]


type TestFunction a = BSL.ByteString -> Either (Error a) T.Text

asIO :: Pretty a => TestFunction a -> FilePath -> IO BSL.ByteString
asIO f = fmap (either errorgen (BSL.fromStrict . encodeUtf8) . f) . BSL.readFile

errorgen :: PrettyPlc a => a -> BSL.ByteString
errorgen = BSL.fromStrict . encodeUtf8 . prettyPlcDefText

asGolden :: Pretty a => TestFunction a -> TestName -> TestTree
asGolden f file = goldenVsString file (file ++ ".golden") (asIO f file)

testsType :: [FilePath] -> TestTree
testsType = testGroup "golden type synthesis tests" . fmap (asGolden printType)

propSizeOfInteger :: Property
propSizeOfInteger = property $ do
    i <- forAll . Gen.integral $ Range.linearFrom 0 (-10000) 10000
    Hedgehog.assert $ checkBoundsInt (sizeOfInteger i) i

unitSizeOfInteger :: IO ()
unitSizeOfInteger
    = foldMap (\(i, s) -> sizeOfInteger i @?= s)
    [ (0, 1)
    , (-1  , 1), (1  , 1)
    , (-127, 1), (127, 1)
    , (-128, 1), (128, 2)
    , (-129, 2), (129, 2)
    ]

testsSizeOfInteger :: TestTree
testsSizeOfInteger
    = testGroup "sizeOfInteger"
    [ testCase     "unit" unitSizeOfInteger
    , testProperty "prop" propSizeOfInteger
    ]

testsNormalizeType :: [FilePath] -> TestTree
testsNormalizeType = testGroup "golden type synthesis + normalization tests" . fmap (asGolden (printNormalizeType True))

testsGolden :: [FilePath] -> TestTree
testsGolden
    = testGroup "golden tests"
    . fmap (asGolden (format $ defPrettyConfigPlcClassic defPrettyConfigPlcOptions))

testsRewrite :: [FilePath] -> TestTree
testsRewrite
    = testGroup "golden rewrite tests"
    . fmap (asGolden (format $ debugPrettyConfigPlcClassic defPrettyConfigPlcOptions))

testEqTerm :: Bool
testEqTerm =
    let
        xName = Name () "x" (Unique 0)
        yName = Name () "y" (Unique 1)

        varX = Var () xName
        varY = Var () yName

        varType = TyVar () (TyName (Name () "a" (Unique 2)))

        lamX = LamAbs () xName varType varX
        lamY = LamAbs () yName varType varY

        -- [(lam x a x) x]
        term0 = Apply () lamX varX
        -- [(lam y a y) x]
        term1 = Apply () lamY varX

    in
        term0 == term1

testRebindShadowedVariable :: Bool
testRebindShadowedVariable =
    let
        xName = TyName (Name () "x" (Unique 0))
        yName = TyName (Name () "y" (Unique 1))

        varX = TyVar () xName
        varY = TyVar () yName

        typeKind = Type ()

        -- (all x (type) (fun (all y (type) y) x))
        type0 = TyForall () xName typeKind (TyFun () (TyForall () yName typeKind varY) varX)
        -- (all x (type) (fun (all x (type) x) x))
        type1 = TyForall () xName typeKind (TyFun () (TyForall () xName typeKind varX) varX)
    in
        type0 == type1

testRebindCapturedVariable :: Bool
testRebindCapturedVariable =
    let
        wName = TyName (Name () "w" (Unique 0))
        xName = TyName (Name () "x" (Unique 1))
        yName = TyName (Name () "y" (Unique 2))
        zName = TyName (Name () "z" (Unique 3))

        varW = TyVar () wName
        varX = TyVar () xName
        varY = TyVar () yName
        varZ = TyVar () zName

        typeKind = Type ()

        -- (all y (type) (all z (type) (fun y z)))
        typeL1 = TyForall () yName typeKind (TyForall () zName typeKind (TyFun () varY varZ))
        -- (all x (type) (all y (type) (fun x y)))
        typeR1 = TyForall () xName typeKind (TyForall () yName typeKind (TyFun () varX varY))

        -- (all z (type) (fun (all w (all x (type) (fun w x))))) z)
        typeL2
            = TyForall () zName typeKind
            $ TyFun ()
                (TyForall () wName typeKind $ TyForall () xName typeKind (TyFun () varW varX))
                varZ
        -- (all x (type) (fun (all x (all y (type) (fun x y))))) x)
        typeR2
            = TyForall () xName typeKind
            $ TyFun ()
                (TyForall () xName typeKind $ TyForall () yName typeKind (TyFun () varX varY))
                varX
    in
        [typeL1, typeL2] == [typeR1, typeR2]

tests :: TestTree
tests = testCase "example programs" $ fold
    [ fmt "(program 0.1.0 [(builtin addInteger) x y])" @?= Right "(program 0.1.0\n  [ [ (builtin addInteger) x ] y ]\n)"
    , fmt "(program 0.1.0 doesn't)" @?= Right "(program 0.1.0\n  doesn't\n)"
    , fmt "{- program " @?= Left (ParseErrorE (LexErr "Error in nested comment at line 1, column 12"))
    , testRebindShadowedVariable @?= True
    , testRebindCapturedVariable @?= True
    , testEqTerm @?= True
    ]
    where
        fmt :: BSL.ByteString -> Either (Error AlexPosn) T.Text
        fmt = format cfg
        cfg = defPrettyConfigPlcClassic defPrettyConfigPlcOptions
