module Main where

import           Control.Monad.Except
import           Data.Coolean
import           Data.Either
import           Language.PlutusCore
import           Language.PlutusCore.Generators.NEAT.Spec
import           Language.PlutusCore.Generators.NEAT.Type
import           Language.PlutusCore.Normalize
import           Test.Tasty
import           Test.Tasty.HUnit

import           MAlonzo.Code.Main                        (checkKindAgda, inferKindAgda, normalizeTypeAgda, inferTypeAgda, checkTypeAgda)
import           MAlonzo.Code.Scoped                      (deBruijnifyK, unDeBruijnifyK)

import           Language.PlutusCore.DeBruijn
import           Raw                                      hiding (TypeError, tynames)


main :: IO ()
main = defaultMain $ allTests defaultGenOptions

allTests :: GenOptions -> TestTree
allTests genOpts = testGroup "NEAT"
  [ testCaseGen "soundness"
      genOpts
      (Type ())
      prop_checkKindSound
  , testCaseGen "normalization"
      genOpts
      (Type ())
      prop_normalizePreservesKind
  , testCaseGen "normalizationSound"
      genOpts
      (Type ())
      prop_normalizeTypeSound
  , testCaseGen "normalizationAgree"
      genOpts
      (Type ())
      prop_normalizeTypeSame
  , testCaseGen "kindInferAgree"
      genOpts
      (Type ())
      prop_kindInferSame
  , testCaseGen "typeInfer"
      genOpts
      (Type (),TyFunG (TyBuiltinG TyIntegerG) (TyBuiltinG TyIntegerG))
      prop_typeinfer
  , testCaseGen "typeCheck"
      genOpts
      (Type (),TyFunG (TyBuiltinG TyIntegerG) (TyBuiltinG TyIntegerG))
      prop_typecheck
  ]

-- check that Agda agrees that the given type is correct
prop_checkKindSound :: Kind () -> ClosedTypeG -> ExceptT TestFail Quote ()
prop_checkKindSound k tyG = do
   ty <- withExceptT GenError $ convertClosedType tynames k tyG
   tyDB <- withExceptT FVErrorP $ deBruijnTy ty
   withExceptT AgdaErrorP $
     case checkKindAgda (AlexPn 0 0 0 <$ tyDB) (deBruijnifyK (convK k)) of
       Just _  -> return ()
       Nothing -> throwError ()

-- check that the Agda type normalizer doesn't mangle the kind
prop_normalizePreservesKind :: Kind ()
                            -> ClosedTypeG
                            -> ExceptT TestFail Quote ()
prop_normalizePreservesKind k tyG = do
  ty  <- withExceptT GenError $ convertClosedType tynames k tyG
  tyDB <- withExceptT FVErrorP $ deBruijnTy ty
  tyN <- withExceptT AgdaErrorP $
    case normalizeTypeAgda (AlexPn 0 0 0 <$ tyDB) of
      Just tyN -> return tyN
      Nothing  -> throwError ()
  withExceptT AgdaErrorP $
    case checkKindAgda (AlexPn 0 0 0 <$ tyN) (deBruijnifyK (convK k)) of
      Just _  -> return ()
      Nothing -> throwError ()

-- compare the NEAT type normalizer against the Agda normalizer
prop_normalizeTypeSound :: Kind ()
                        -> ClosedTypeG
                        -> ExceptT TestFail Quote ()
prop_normalizeTypeSound k tyG = do
  ty <- withExceptT GenError $ convertClosedType tynames k tyG
  tyDB <- withExceptT FVErrorP $ deBruijnTy ty
  tyN1 <- withExceptT AgdaErrorP $ case normalizeTypeAgda (AlexPn 0 0 0 <$ tyDB) of
    Just tyN -> return tyN
    Nothing  -> throwError ()
  ty1 <- withExceptT FVErrorP $ unDeBruijnTy tyN1
  ty2 <- withExceptT GenError $ convertClosedType tynames k (normalizeTypeG tyG)
  unless (ty1 == (AlexPn 0 0 0 <$ ty2)) $
    throwCtrex (CtrexNormalizeConvertCommuteTypes k ty (() <$ ty1) ty2)

-- compare the production type normalizer against the Agda type normalizer
prop_normalizeTypeSame :: Kind ()
                        -> ClosedTypeG
                        -> ExceptT TestFail Quote ()
prop_normalizeTypeSame k tyG = do
  ty <- withExceptT GenError $ convertClosedType tynames k tyG
  tyDB <- withExceptT FVErrorP $ deBruijnTy ty
  tyN1 <- withExceptT AgdaErrorP $
    case normalizeTypeAgda (AlexPn 0 0 0 <$ tyDB) of
      Just tyN -> return tyN
      Nothing  -> throwError ()
  ty1 <- withExceptT FVErrorP $ unDeBruijnTy tyN1
  ty2 <- withExceptT TypeError $ unNormalized <$> normalizeType ty
  unless (ty1 == (AlexPn 0 0 0 <$ ty2)) $
    throwCtrex (CtrexNormalizeConvertCommuteTypes k ty (() <$ ty1) ty2)

-- compare the production kind inference against the Agda 
prop_kindInferSame :: Kind ()
                   -> ClosedTypeG
                   -> ExceptT TestFail Quote ()
prop_kindInferSame k tyG = do
  ty <- withExceptT GenError $ convertClosedType tynames k tyG
  tyDB <- withExceptT FVErrorP $ deBruijnTy ty
  k' <- withExceptT AgdaErrorP $ case inferKindAgda (AlexPn 0 0 0 <$ tyDB) of
    Just k' -> return k'
    Nothing -> throwError ()
  k'' <- withExceptT TypeError $ inferKind defConfig (() <$ ty)
  unless (unconvK (unDeBruijnifyK k') == k'') $ throwError (AgdaErrorP ()) -- FIXME

-- try to typecheck a term
prop_typeinfer :: (Kind (), ClosedTypeG) -> ClosedTermG -> ExceptT TestFail Quote ()
prop_typeinfer (k , tyG) tmG = do
  tm <- withExceptT GenError $ convertClosedTerm tynames names tyG tmG
  tmDB <- withExceptT FVErrorP $ deBruijnTerm tm
  withExceptT AgdaErrorP $
    case inferTypeAgda (AlexPn 0 0 0 <$ tmDB) of
      Just _  -> return ()
      Nothing -> throwError ()
   
-- try to typecheck a term
prop_typecheck :: (Kind (), ClosedTypeG) -> ClosedTermG -> ExceptT TestFail Quote ()
prop_typecheck (k , tyG) tmG = do
  ty <- withExceptT GenError $ convertClosedType tynames k tyG
  tyDB <- withExceptT FVErrorP $ deBruijnTy ty
  tm <- withExceptT GenError $ convertClosedTerm tynames names tyG tmG
  tmDB <- withExceptT FVErrorP $ deBruijnTerm tm
  withExceptT AgdaErrorP $
    case checkTypeAgda (AlexPn 0 0 0 <$ tyDB) (AlexPn 0 0 0 <$ tmDB) of
      Just _  -> return ()
      Nothing -> throwError ()
   
