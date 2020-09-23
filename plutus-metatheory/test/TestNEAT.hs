module Main where

import           Control.Monad.Except
import           Data.Coolean
import           Data.Either
import           Language.PlutusCore
import           Language.PlutusCore.Generators.NEAT.PropTest
import           Language.PlutusCore.Normalize
import           Test.Tasty
import           Test.Tasty.HUnit

import           MAlonzo.Code.Main                            (checkKindAgda, inferKindAgda, normalizeTypeAgda)
import           MAlonzo.Code.Scoped                          (deBruijnifyK, unDeBruijnifyK)

import           Language.PlutusCore.DeBruijn
import           Raw


main :: IO ()
main = defaultMain allTests

allTests :: TestTree
allTests = testGroup "all tests"
  [ testCaseCount "soundness" $
      testTyProp size star prop_checkKindSound
  , testCaseCount "normalization" $
      testTyProp size star prop_normalizePreservesKind
  , testCaseCount "normalizationSound" $
      testTyProp size star prop_normalizeTypeSound
  , testCaseCount "normalizationAgree" $
      testTyProp size star prop_normalizeTypeSame
  , testCaseCount "kindInferAgree" $
      testTyProp size star prop_kindInferSame
  ]

testCaseCount :: String -> IO Integer -> TestTree
testCaseCount name act = testCaseInfo name $
  liftM (\i -> show i ++ " types generated") act


-- NEAT settings

size :: Int
size = 10

star :: Kind ()
star = Type ()

-- |Check if the type/kind checker or generation threw any errors.
isSafe :: ExceptT (ErrorP a) Quote a -> Cool
isSafe = toCool . isRight . runQuote . runExceptT

prop_checkKindSound :: TyProp
prop_checkKindSound k _ tyQ = isSafe $ do
  ty <- withExceptT GenErrorP tyQ
  tyDB <- withExceptT FVErrorP $ deBruijnTy ty
  withExceptT AgdaErrorP $ case checkKindAgda (AlexPn 0 0 0 <$ tyDB) (deBruijnifyK (convK k)) of
    Just _  -> return ()
    Nothing -> throwError ()

prop_normalizePreservesKind :: TyProp
prop_normalizePreservesKind k _ tyQ = isSafe $ do
  ty  <- withExceptT GenErrorP tyQ
  tyDB <- withExceptT FVErrorP $ deBruijnTy ty
  tyN <- withExceptT AgdaErrorP $ case normalizeTypeAgda (AlexPn 0 0 0 <$ tyDB) of
    Just tyN -> return tyN
    Nothing  -> throwError ()
  withExceptT AgdaErrorP $ case checkKindAgda (AlexPn 0 0 0 <$ tyN) (deBruijnifyK (convK k)) of
    Just _  -> return ()
    Nothing -> throwError ()

-- the agda implementation throws names away, so I guess we need to compare deBruijn terms
prop_normalizeTypeSound :: TyProp
prop_normalizeTypeSound k tyG tyQ = isSafe $ do
  ty <- withExceptT GenErrorP tyQ
  tyDB <- withExceptT FVErrorP $ deBruijnTy ty
  tyN1 <- withExceptT AgdaErrorP $ case normalizeTypeAgda (AlexPn 0 0 0 <$ tyDB) of
    Just tyN -> return tyN
    Nothing  -> throwError ()
  ty1 <- withExceptT FVErrorP $ unDeBruijnTy tyN1

  ty2 <- withExceptT GenErrorP $ toClosedType k (normalizeTypeG tyG)
  return (ty1 == (AlexPn 0 0 0 <$ ty2))

prop_normalizeTypeSame :: TyProp
prop_normalizeTypeSame k tyG tyQ = isSafe $ do
  ty <- withExceptT GenErrorP tyQ
  tyDB <- withExceptT FVErrorP $ deBruijnTy ty
  tyN1 <- withExceptT AgdaErrorP $ case normalizeTypeAgda (AlexPn 0 0 0 <$ tyDB) of
    Just tyN -> return tyN
    Nothing  -> throwError ()
  ty1 <- withExceptT FVErrorP $ unDeBruijnTy tyN1

  ty2 <- withExceptT TypeErrorP $ unNormalized <$> normalizeType ty
  return (ty1 == (AlexPn 0 0 0 <$ ty2))

prop_kindInferSame :: TyProp
prop_kindInferSame k tyG tyQ = isSafe $ do
  ty <- withExceptT GenErrorP tyQ
  tyDB <- withExceptT FVErrorP $ deBruijnTy ty
  k' <- withExceptT AgdaErrorP $ case inferKindAgda (AlexPn 0 0 0 <$ tyDB) of
    Just k' -> return k'
    Nothing -> throwError ()
  k'' <- withExceptT TypeErrorP $ inferKind defConfig (True <$ ty)
  return (unconvK (unDeBruijnifyK k') == k'')
