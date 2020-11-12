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
                                                            normalizeTypeAgda, normalizeTypeTermAgda, runCKAgda,
                                                            runLAgda, runTCEKVAgda, runTCKAgda)
import           MAlonzo.Code.Scoped                       (deBruijnifyK, unDeBruijnifyK)

import           Language.PlutusCore.DeBruijn
import           Raw                                       hiding (TypeError, tynames)

main :: IO ()
main = defaultMain $ allTests defaultGenOptions

allTests :: GenOptions -> TestTree
allTests genOpts = testGroup "NEAT"
  [ bigTest "type-level"
      genOpts
      (Type ())
      (packAssertion prop_Type)
  , bigTest "term-level"
      genOpts
      (TyFunG (TyBuiltinG TyIntegerG) (TyBuiltinG TyIntegerG))
      (packAssertion prop_Term)
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



-- one term-level test to rule them all
prop_Term :: ClosedTypeG -> ClosedTermG -> ExceptT TestFail Quote ()
prop_Term tyG tmG = do
  -- get a production named type
  ty <- withExceptT GenError $ convertClosedType tynames (Type ()) tyG
  -- get a production de Bruijn type
  tyDB <- withExceptT FVErrorP $ deBruijnTy ty
  -- get a production named term
  tm <- withExceptT GenError $ convertClosedTerm tynames names tyG tmG
  -- get a production de Bruijn term
  tmDB <- withExceptT FVErrorP $ deBruijnTerm tm

  -- 1. check the term in the type
  withExceptT (const $ Ctrex (CtrexTypeCheckFail tyG tmG)) $ liftEither $
    checkTypeAgda tyDB tmDB

  -- 2. run production CK against metatheory CK
  tmPlcCK <- withExceptT CkP $ liftEither $ evaluateCk mempty tm
  tmCK <- withExceptT (const $ Ctrex (CtrexTermEvaluationFail tyG tmG)) $
    liftEither $ runCKAgda tmDB
  tmCKN <- withExceptT FVErrorP $ unDeBruijnTerm tmCK
  unless (tmPlcCK == tmCKN) $
    throwCtrex (CtrexTermEvaluationMismatch tyG tmG [tmPlcCK,tmCKN])

  -- 3. run all the metatheory evaluators against each other. Taking
  -- care to normalize the types in the output of runCKAgda. The other
  -- versions return terms with already normalized types.
  let evs = [runLAgda,runCKAgda >=> normalizeTypeTermAgda,runTCKAgda,runTCEKVAgda]
  let tmEvsM = map ($ tmDB) evs
  tmEvs <- withExceptT (const $ Ctrex (CtrexTermEvaluationFail tyG tmG)) $
    liftEither $ sequence tmEvsM
  tmEvsN <- withExceptT FVErrorP $ traverse unDeBruijnTerm tmEvs

  unless (length (nub tmEvsN) == 1) $ throwCtrex (CtrexTermEvaluationMismatch tyG tmG tmEvsN)
