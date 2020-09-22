module Main where

import           Control.Monad.Except
import           Data.Coolean
import           Data.Either
import           Data.List

import           Language.PlutusCore
import           Language.PlutusCore.Evaluation.Machine.Ck
import           Language.PlutusCore.Generators.NEAT.Spec
import           Language.PlutusCore.Generators.NEAT.Type
import           Language.PlutusCore.Lexer
import           Language.PlutusCore.Normalize
import           Test.Tasty
import           Test.Tasty.HUnit

import           MAlonzo.Code.Main                         (checkKindAgda, checkTypeAgda, inferKindAgda, inferTypeAgda,
                                                            normalizeTypeAgda, runCKAgda, runLAgda, runTCEKCAgda,
                                                            runTCEKVAgda, runTCKAgda)
import           MAlonzo.Code.Scoped                       (deBruijnifyK, unDeBruijnifyK)

import           Language.PlutusCore.DeBruijn
import           Raw                                       hiding (TypeError, tynames)

main :: IO ()
main = defaultMain $ allTests defaultGenOptions

allTests :: GenOptions -> TestTree
allTests genOpts = testGroup "NEAT"
  [ testCaseGen "type-level"
      genOpts
      (Type ())
      prop_Type
  , testCaseGen "typeInfer"
      genOpts
      (Type (),TyFunG (TyBuiltinG TyIntegerG) (TyBuiltinG TyIntegerG))
      prop_typeinfer
  , testCaseGen "typeCheck"
      genOpts
      (Type (),TyFunG (TyBuiltinG TyIntegerG) (TyBuiltinG TyIntegerG))
      prop_typecheck
  , testCaseGen "run_plcCK_vs_CK"
      genOpts
      (Type (),TyFunG (TyBuiltinG TyIntegerG) (TyBuiltinG TyIntegerG))
      prop_run_plcCK_vs_CK
   , testCaseGen "Agda model evaluators agree"
      genOpts
      (Type (),TyFunG (TyBuiltinG TyIntegerG) (TyBuiltinG TyIntegerG))
      (prop_runList [runLAgda,runCKAgda,runTCKAgda,runTCEKVAgda,runTCEKCAgda])
  ]


-- one type-level test to rule them all
prop_Type :: Kind () -> ClosedTypeG -> ExceptT TestFail Quote ()
prop_Type k tyG = do
  -- get a production named type:
  ty <- withExceptT GenError $ convertClosedType tynames k tyG
  -- get a production De Bruijn type:
  tyDB <- withExceptT FVErrorP $ deBruijnTy ty
  
  -- 1. check soundness of Agda kindchecker with respect to NEAT:
  withExceptT (const $ Ctrex (CtrexKindCheckFail k tyG)) $ liftEither $
    checkKindAgda tyDB (deBruijnifyK (convK k))
  -- infer kind using Agda kind inferer:
  k1 <- withExceptT (const $ Ctrex (CtrexKindCheckFail k tyG)) $
    liftEither $ inferKindAgda tyDB
  -- infer kind using production kind inferer:
  k2 <- withExceptT TypeError $ inferKind defConfig ty

  -- 2. check that production and Agda kind inferer agree:
  unless (unconvK (unDeBruijnifyK k1) == k2) $
    throwCtrex (CtrexKindMismatch k tyG (unconvK (unDeBruijnifyK k1)) k2)

    
  -- normalize type using Agda type normalizer:
  ty' <- withExceptT (const $ Ctrex (CtrexTypeNormalizationFail k tyG)) $
    liftEither $ normalizeTypeAgda tyDB

  -- 3. check that the Agda type normalizer doesn't mange the kind:
  withExceptT (const $ Ctrex (CtrexKindPreservationFail k tyG)) $
    liftEither $ checkKindAgda ty' (deBruijnifyK (convK k))

  -- convert Agda normalized type back to named notation:
  ty1 <- withExceptT FVErrorP $ unDeBruijnTy ty'
  -- normalize NEAT type using NEAT type normalizer:
  ty2 <- withExceptT GenError $ convertClosedType tynames k (normalizeTypeG tyG)

  -- 4. check the Agda type normalizer agrees with the NEAT type normalizer:
  unless (ty1 == ty2) $
    throwCtrex (CtrexNormalizeConvertCommuteTypes k tyG ty1 ty2)
  
-- try to infer the type of a term
prop_typeinfer :: (Kind (), ClosedTypeG) -> ClosedTermG -> ExceptT TestFail Quote ()
prop_typeinfer (k , tyG) tmG = do
  tm <- withExceptT GenError $ convertClosedTerm tynames names tyG tmG
  tmDB <- withExceptT FVErrorP $ deBruijnTerm tm
  withExceptT (const $ Ctrex (CtrexTypeCheckFail tyG tmG)) $ liftEither $
    inferTypeAgda tmDB
  return ()

-- try to typecheck a term
prop_typecheck :: (Kind (), ClosedTypeG) -> ClosedTermG
               -> ExceptT TestFail Quote ()
prop_typecheck (k , tyG) tmG = do
  ty <- withExceptT GenError $ convertClosedType tynames k tyG
  tyDB <- withExceptT FVErrorP $ deBruijnTy ty
  tm <- withExceptT GenError $ convertClosedTerm tynames names tyG tmG
  tmDB <- withExceptT FVErrorP $ deBruijnTerm tm
  withExceptT (const $ Ctrex (CtrexTypeCheckFail tyG tmG)) $ liftEither $
    checkTypeAgda tyDB tmDB
  return ()

prop_run_plcCK_vs_CK :: (Kind (), ClosedTypeG) -> ClosedTermG -> ExceptT TestFail Quote ()
prop_run_plcCK_vs_CK (k , tyG) tmG = do
  tm <- withExceptT GenError $ convertClosedTerm tynames names tyG tmG
  tmPlcCK <- withExceptT CkP $ liftEither $ evaluateCk mempty tm
  tmDB <- withExceptT FVErrorP $ deBruijnTerm tm
  tmCK <- withExceptT (const $ Ctrex (CtrexTermEvaluationFail tyG tmG)) $
    liftEither $ runCKAgda tmDB
  tmCKN <- withExceptT FVErrorP $ unDeBruijnTerm tmCK
  unless (tmPlcCK == tmCKN) $ throwCtrex (CtrexTermEvaluationMismatch tyG tmG [tmPlcCK,tmCKN])

type TERM = Term TyDeBruijn DeBruijn DefaultUni ()

prop_runList :: [(TERM -> Either ERROR TERM)]
            -> (Kind (), ClosedTypeG)
            -> ClosedTermG -> ExceptT TestFail Quote ()
prop_runList evs (k , tyG) tmG = do
  tm <- withExceptT GenError $ convertClosedTerm tynames names tyG tmG
  tmDB <- withExceptT FVErrorP $ deBruijnTerm tm
  let tmEvsM = evs <*> [tmDB]
  tmEvs <- withExceptT (const $ Ctrex (CtrexTermEvaluationFail tyG tmG)) $
    liftEither $ sequence tmEvsM
  tmEvsN <- withExceptT FVErrorP $ sequence (unDeBruijnTerm <$> tmEvs)
  unless (length (nub tmEvsN) == 1) $ throwCtrex (CtrexTermEvaluationMismatch tyG tmG tmEvsN)
