-- editorconfig-checker-disable-file
module Main where

import Control.Monad (unless)
import Control.Monad.Except (ExceptT (..), catchError, liftEither, withExceptT)
import Data.Coolean
import Data.Either
import Data.List
import PlutusCore
import PlutusCore.Compiler.Erase
import PlutusCore.Evaluation.Machine.Ck
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import PlutusCore.Generators.NEAT.Spec
import PlutusCore.Generators.NEAT.Term
import PlutusCore.Normalize
import PlutusCore.Pretty
import Test.Tasty
import Test.Tasty.HUnit
import UntypedPlutusCore qualified as U
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as U

import MAlonzo.Code.Evaluator.Term (checkKindAgda, checkTypeAgda, inferKindAgda, inferTypeAgda,
                                    normalizeTypeAgda, normalizeTypeTermAgda, runTCEKAgda,
                                    runTCKAgda, runTLAgda, runUAgda)
import PlutusCore.DeBruijn
import Raw hiding (TypeError, tynames)

import Debug.Trace

main :: IO ()
main = defaultMain allTests

allTests :: TestTree
allTests = testGroup "NEAT"
  [ localOption (GenDepth 12) $
    bigTest "type-level"
      (Type ())
      (packAssertion prop_Type)
  , localOption (GenDepth 18) $
    bigTest "term-level"
      (TyBuiltinG TyUnitG)
      (packAssertion prop_Term)
  ]

-- one type-level test to rule them all
prop_Type :: Kind () -> ClosedTypeG -> ExceptT TestFail Quote ()
prop_Type k tyG = do
  tcConfig <- withExceptT TypeError $ getDefTypeCheckConfig ()

  -- get a production named type:
  tyH <- withExceptT GenError $ convertClosedType tynames k tyG
  let tyA = fromHaskellType tyH
  -- get a production De Bruijn type:
  tyDB <- withExceptT FVErrorP $ deBruijnTy tyA

  -- 1. check soundness of Agda kindchecker with respect to NEAT:
  withExceptT (const $ Ctrex (CtrexKindCheckFail k tyG)) $ liftEither $
    checkKindAgda tyDB (convK k)
  -- infer kind using Agda kind inferer:
  k1a <- withExceptT (const $ Ctrex (CtrexKindCheckFail k tyG)) $
    liftEither $ inferKindAgda tyDB
  let k1 = unconvK k1a
  -- infer kind using production kind inferer:
  k2 <- withExceptT TypeError $ inferKind defKindCheckConfig tyH

  -- 2. check that production and Agda kind inferer agree:
  unless (k1 == k2) $
    throwCtrex (CtrexKindMismatch k tyG k1 k2)


  -- normalize type using Agda type normalizer:
  ty' <- withExceptT (const $ Ctrex (CtrexTypeNormalizationFail k tyG)) $
    liftEither $ normalizeTypeAgda tyDB

  -- 3. check that the Agda type normalizer doesn't mange the kind:
  withExceptT (const $ Ctrex (CtrexKindPreservationFail k tyG)) $
    liftEither $ checkKindAgda ty' (convK k)

  -- convert Agda normalized type back to named notation:
  ty1 <- withExceptT FVErrorP $ unDeBruijnTy ty'
  -- normalize NEAT type using NEAT type normalizer:
  ty2 <- withExceptT GenError $ convertClosedType tynames k (normalizeTypeG tyG)
  let ty1H = toHaskellType ty1
      ty2H = ty2

  -- 4. check the Agda type normalizer agrees with the NEAT type normalizer:
  unless (ty1H == ty2H) $
    throwCtrex (CtrexNormalizeConvertCommuteTypes k tyG ty1H ty2H)



-- one term-level test to rule them all
prop_Term :: ClosedTypeG -> ClosedTermG -> ExceptT TestFail Quote ()
prop_Term tyG tmG = do
  -- get a production named type
  tyH <- withExceptT GenError $ convertClosedType tynames (Type ()) tyG
  let tyA = fromHaskellType tyH
  -- get a production de Bruijn type
  tyDBH <- withExceptT FVErrorP $ deBruijnTy tyH
  let tyDBA = fromHaskellType tyDBH
  -- get a production named term
  tmH <- withExceptT GenError $ convertClosedTerm tynames names tyG tmG
  let tmA = fromHaskellTerm tmH
  -- get a production de Bruijn term
  tmDBH <- withExceptT FVErrorP $ deBruijnTerm tmH
  let tmDBA = fromHaskellTerm tmDBH

  -- 1. check the term in the type
  withExceptT (const $ Ctrex (CtrexTypeCheckFail tyG tmG)) $ liftEither $
    checkTypeAgda tyDBA tmDBA

  -- 2. run production CK against metatheory CK
  tmPlcCK <- withExceptT CkP $ liftEither $
    evaluateCkNoEmit defaultBuiltinsRuntimeForTesting tmH `catchError` handleError tyH
  tmCKA <- withExceptT (const $ Ctrex (CtrexTermEvaluationFail "0" tyG tmG)) $
    liftEither $ runTCKAgda tmDBA
  tmCKNA <- withExceptT FVErrorP $ unDeBruijnTerm tmCKA
  let tmCKNH = toHaskellTerm tmCKNA
  unless (tmPlcCK == tmCKNH) $
    throwCtrex (CtrexTermEvaluationMismatch tyG tmG [("prod CK",tmPlcCK),("meta CK",tmCKNH)])

  -- 3. run all the metatheory evaluators against each other. Taking
  -- care to normalize the types in the output of runCKAgda. The other
  -- versions return terms with already normalized types.
  let namedEvs = [("meta red",runTLAgda),("meta CK",runTCKAgda),("meta CEK",runTCEKAgda)]
  let (ss,evs) = unzip namedEvs
  let tmEvsM = map ($ tmDBA) evs
  tmEvs <- withExceptT (const $ Ctrex (CtrexTermEvaluationFail "typed" tyG tmG)) $
    liftEither $ sequence tmEvsM
  tmEvsN <- withExceptT FVErrorP $ traverse unDeBruijnTerm tmEvs
  let tmEvsHN = fmap toHaskellTerm tmEvsN

  unless (length (nub tmEvsHN) == 1) $ throwCtrex (CtrexTermEvaluationMismatch tyG tmG (zip ss tmEvsHN))
  -- 4. untyped_reduce . erase == erase . typed_reduce

  -- erase original named term
  let tmUH = eraseTerm tmH
  -- turn it into an untyped de Bruijn term
  tmUDBH <- withExceptT FVErrorP $ U.deBruijnTerm tmUH
  let tmUDBA = fromHaskellUTerm tmUDBH
  -- reduce the untyped term
  tmUDBA' <- case runUAgda tmUDBA of
      Left (RuntimeError UserError) -> pure $ U.Error ()
      _ -> withExceptT (\e -> Ctrex (CtrexTermEvaluationFail "untyped CEK" tyG tmG))
          $ liftEither $ runUAgda tmUDBA
  -- turn it back into a named term
  tmUA' <- withExceptT FVErrorP $ U.unDeBruijnTerm tmUDBA'
  let tmUH' = toHaskellUTerm tmUA'
  -- reduce the original de Bruijn typed term
  tmDBA'' <- withExceptT (\e -> Ctrex (CtrexTermEvaluationFail "typed CEK" tyG tmG)) $
    liftEither $ runTCEKAgda tmDBA
  -- turn it back into a named term
  tmA'' <- withExceptT FVErrorP $ unDeBruijnTerm tmDBA''
  -- erase it after the fact
  let tmH'' = toHaskellTerm tmA''
  let tmUH'' = eraseTerm tmH''
  unless (tmUH' == tmUH'') $
    throwCtrex (CtrexUntypedTermEvaluationMismatch tyG tmG [("erase;reduce" , tmUH'),("reduce;erase" , tmUH'')])

  -- 4. run prod untyped CEK against meta untyped CEK
  tmUH''' <- withExceptT UCekP $ liftEither $
    U.evaluateCekNoEmit defaultCekParametersForTesting tmUH'' `catchError` handleUError
  unless (tmUH' == tmUH''') $
    throwCtrex (CtrexUntypedTermEvaluationMismatch tyG tmG [("meta U" , tmUH'),("prod U" , tmUH'')])
