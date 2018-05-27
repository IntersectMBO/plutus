{-# LANGUAGE OverloadedStrings #-}

module Main ( main
            ) where

import qualified Data.ByteString.Lazy as BSL
import           Data.Foldable        (fold)
import           Data.Function        (on)
import qualified Data.List.NonEmpty   as NE
import           Data.Text.Encoding   (encodeUtf8)
import           Hedgehog             hiding (Size, Var)
import qualified Hedgehog.Gen         as Gen
import qualified Hedgehog.Range       as Range
import           Language.PlutusCore
import           Test.Tasty
import           Test.Tasty.Hedgehog
import           Test.Tasty.HUnit

main :: IO ()
main = defaultMain allTests

compareName :: Name a -> Name a -> Bool
compareName = (==) `on` asString

compareTerm :: Eq a => Term a -> Term a -> Bool
compareTerm (Var _ n) (Var _ n')                = compareName n n'
compareTerm (TyAnnot _ t te) (TyAnnot _ t' te') = compareType t t' && compareTerm te te'
compareTerm (TyAbs _ n t) (TyAbs _ n' t')       = compareName n n' && compareTerm t t'
compareTerm (LamAbs _ n t) (LamAbs _ n' t')     = compareName n n' && compareTerm t t'
compareTerm (Apply _ t ts) (Apply _ t' ts')     = compareTerm t t' && and (NE.zipWith compareTerm ts ts')
compareTerm (Fix _ n t) (Fix _ n' t')           = compareName n n' && compareTerm t t'
compareTerm x@Constant{} y@Constant{}           = x == y
compareTerm (TyInst _ t ts) (TyInst _ t' ts')   = compareTerm t t' && and (NE.zipWith compareType ts ts')
compareTerm _ _                                 = False

compareType :: Eq a => Type a -> Type a -> Bool
compareType (TyVar _ n) (TyVar _ n')                 = compareName n n'
compareType (TyFun _ t s) (TyFun _ t' s')            = compareType t t' && compareType s s'
compareType (TyFix _ n k t) (TyFix _ n' k' t')       = compareName n n' && k == k' && compareType t t'
compareType (TyForall _ n k t) (TyForall _ n' k' t') = compareName n n' && k == k' && compareType t t'
compareType x@TyBuiltin{} y@TyBuiltin{}              = x == y
compareType (TyLam _ n k t) (TyLam _ n' k' t')       = compareName n n' && k == k' && compareType t t'
compareType (TyApp _ t ts) (TyApp _ t' ts')          = compareType t t' && and (NE.zipWith compareType ts ts')
compareType _ _                                      = False

compareProgram :: Eq a => Program a -> Program a -> Bool
compareProgram (Program _ v t) (Program _ v' t') = v == v' && compareTerm t t'

genVersion :: MonadGen m => m (Version AlexPosn)
genVersion = Version emptyPosn <$> int' <*> int' <*> int'
    where int' = Gen.integral_ (Range.linear 0 10)

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
    , EqInteger, IntToByteString, IntToByteString, Concatenate, TakeByteString
    , DropByteString, ResizeByteString, SHA2, SHA3, VerifySignature
    , EqByteString, TxHash, BlockNum, BlockTime
    ]

genBuiltin :: MonadGen m => m (Constant AlexPosn)
genBuiltin = Gen.choice [BuiltinName emptyPosn <$> genBuiltinName, genInt, genSize, genBS]
    where int' = Gen.integral_ (Range.linear (-10000000) 10000000)
          size' = Gen.integral_ (Range.linear 8 64)
          string' = BSL.fromStrict <$> Gen.utf8 (Range.linear 0 40) Gen.unicode
          genInt = BuiltinInt emptyPosn <$> size' <*> int'
          genSize = BuiltinSize emptyPosn <$> size'
          genBS = BuiltinBS emptyPosn <$> size' <*> string'

genType :: MonadGen m => m (Type AlexPosn)
genType = simpleRecursive nonRecursive recursive
    where varGen = TyVar emptyPosn <$> genName
          funGen = TyFun emptyPosn <$> genType <*> genType
          lamGen = TyLam emptyPosn <$> genName <*> genKind <*> genType
          forallGen = TyForall emptyPosn <$> genName <*> genKind <*> genType
          fixGen = TyFix emptyPosn <$> genName <*> genKind <*> genType
          applyGen = TyApp emptyPosn <$> genType <*> args genType
          recursive = [funGen, applyGen]
          nonRecursive = [varGen, lamGen, forallGen, fixGen]
          args = Gen.nonEmpty (Range.linear 1 4)

genTerm :: MonadGen m => m (Term AlexPosn)
genTerm = simpleRecursive nonRecursive recursive
    where varGen = Var emptyPosn <$> genName
          annotGen = TyAnnot emptyPosn <$> genType <*> genTerm
          fixGen = Fix emptyPosn <$> genName <*> genTerm
          absGen = TyAbs emptyPosn <$> genName <*> genTerm
          instGen = TyInst emptyPosn <$> genTerm <*> args genType
          lamGen = LamAbs emptyPosn <$> genName <*> genTerm
          applyGen = Apply emptyPosn <$> genTerm <*> args genTerm
          recursive = [fixGen, annotGen, absGen, instGen, lamGen, applyGen]
          nonRecursive = [varGen, Constant emptyPosn <$> genBuiltin]
          args = Gen.nonEmpty (Range.linear 1 4)

genProgram :: MonadGen m => m (Program AlexPosn)
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

allTests :: TestTree
allTests = testGroup "all tests"
    [ tests
    , testProperty "parser round-trip" propParser
    ]

tests :: TestTree
tests = testCase "example programs" $ fold
    [ format "(program 0.1.0 [(con addInteger) x y])" @?= Right "(program 0.1.0 [ (con addInteger) x y ])"
    , format "(program 0.1.0 doesn't)" @?= Right "(program 0.1.0 doesn't)"
    , format "(program 0.1.0 (isa (lam x (fun (type) (type)) y) z))" @?= Right "(program 0.1.0 (isa (lam x (fun (type) (type)) y) z))"
    ]
