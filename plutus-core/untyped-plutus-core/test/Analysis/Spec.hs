{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
module Analysis.Spec where

import Test.Tasty.Extras

import PlutusCore qualified as PLC
import PlutusCore.MkPlc
import PlutusCore.Pretty (prettyPlcReadableDef)
import PlutusCore.Quote
import Test.Tasty
import Test.Tasty.HUnit
import UntypedPlutusCore
import UntypedPlutusCore.Purity

goldenEvalOrder :: String -> Term Name PLC.DefaultUni PLC.DefaultFun () -> TestNested
goldenEvalOrder name tm = nestedGoldenVsDoc name "" (prettyPlcReadableDef $ termEvaluationOrder tm)

-- Should hit Unknown before trying to process the undefined. Shows
-- that the computation is lazy
-- [ [ n m ] (constr 1 [undefined]) ]
dangerTerm :: Term Name PLC.DefaultUni PLC.DefaultFun ()
dangerTerm = runQuote $ do
  n <- freshName "n"
  m <- freshName "m"
  -- The UPLC term type is strict, so it's hard to hide an undefined in there
  -- Take advantage of the fact that it's still using lazy lists for constr
  -- arguments for now.
  pure $ Apply () (Apply () (Var () n) (Var () m)) (Constr () 1 [undefined])

letFun :: Term Name PLC.DefaultUni PLC.DefaultFun ()
letFun = runQuote $ do
  n <- freshName "n"
  let intConst = mkConstant () (1 :: Integer)
  pure $ Apply ()
    (LamAbs () n (mkIterAppNoAnn (Var () n) [intConst, intConst]))
    (Builtin () PLC.AddInteger)

letImpure :: Term Name PLC.DefaultUni PLC.DefaultFun ()
letImpure = runQuote $ do
  n <- freshName "n"
  m <- freshName "m"
  let intConst = mkConstant () (1 :: Integer)
  pure $ Apply ()
    (LamAbs () n (mkIterAppNoAnn (Var () n) [intConst, intConst]))
    -- don't need this to be well-scoped
    (Apply () (Var () m) intConst)

evalOrder :: TestTree
evalOrder = runTestNestedIn ["untyped-plutus-core", "test", "Analysis"] $ testNested "evalOrder"
  [ goldenEvalOrder "letFun" letFun
  , goldenEvalOrder "letImpure" letImpure
  , pure $ testCase "evalOrderLazy" $ 4 @=? length (unEvalOrder $ termEvaluationOrder dangerTerm)
  ]
