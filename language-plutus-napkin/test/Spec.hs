{-# LANGUAGE OverloadedStrings #-}

module Main ( main
            ) where

import qualified Data.ByteString.Lazy as BSL
import           Data.Foldable        (fold)
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

genVersion :: MonadGen m => m (Version AlexPosn)
genVersion = Version emptyPosn <$> int' <*> int' <*> int'
    where int' = Gen.integral_ (Range.linear 0 10)

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

genType :: MonadGen m => m (Type AlexPosn)
genType = simpleRecursive nonRecursive recursive
    where varGen = TyVar emptyPosn <$> genName
          funGen = TyFun emptyPosn <$> genType <*> genType
          lamGen = TyLam emptyPosn <$> genName <*> genKind <*> genType
          recursive = [funGen]
          nonRecursive = [varGen, lamGen]

genTerm :: MonadGen m => m (Term AlexPosn)
genTerm = simpleRecursive nonRecursive recursive
    where varGen = Var emptyPosn <$> genName
          annotGen = TyAnnot emptyPosn <$> genType <*> genTerm
          fixGen = Fix emptyPosn <$> genName <*> genTerm
          absGen = TyAbs emptyPosn <$> genName <*> genTerm
          instGen = TyInst emptyPosn <$> genTerm <*> genType
          lamGen = LamAbs emptyPosn <$> genName <*> genTerm
          recursive = [fixGen, annotGen, absGen, instGen, lamGen]
          nonRecursive = [varGen]

genProgram :: MonadGen m => m (Program AlexPosn)
genProgram = Program emptyPosn <$> genVersion <*> genTerm

emptyPosn :: AlexPosn
emptyPosn = AlexPn 0 0 0

propParser :: Property
propParser = property $ do
    prog <- forAll genProgram
    let nullPosn = fmap (pure emptyPosn)
        reprint = BSL.fromStrict . encodeUtf8 . prettyText
    Right (nullPosn prog) === (nullPosn <$> parse (reprint prog))

allTests :: TestTree
allTests = testGroup "all tests"
    [ tests
    , testProperty "parser round-trip" propParser
    ]
tests :: TestTree
tests = testCase "example programs" $ fold
    [ format "(program 0.1.0 [(builtin addInteger) x y])" @?= Right "(program 0.1.0 [ (builtin addInteger) x y ])"
    , format "(program 0.1.0 doesn't)" @?= Right "(program 0.1.0 doesn't)"
    , format "(program 0.1.0 (isa (lam x (fun (type) (type)) y) z))" @?= Right "(program 0.1.0 (isa (lam x (fun (type) (type)) y) z))"
    ]
