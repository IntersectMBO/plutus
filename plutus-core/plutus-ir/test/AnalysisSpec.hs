{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
module AnalysisSpec where

import Test.Tasty.Extras

import PlutusCore qualified as PLC
import PlutusCore.Pretty (prettyPlcReadableDef)
import PlutusCore.Quote
import PlutusIR
import PlutusIR.Analysis.VarInfo
import PlutusIR.Parser
import PlutusIR.Purity
import PlutusIR.Test
import PlutusIR.Transform.Rename ()
import PlutusPrelude (def)
import Test.Tasty.HUnit

computeEvalOrder
  :: Term TyName Name PLC.DefaultUni PLC.DefaultFun a
  -> EvalOrder TyName Name PLC.DefaultUni PLC.DefaultFun a
computeEvalOrder tm = termEvaluationOrder def (termVarInfo tm) tm

-- Avoids traversing the term to compute the var info
computeEvalOrderCoarse
  :: Term TyName Name PLC.DefaultUni PLC.DefaultFun a
  -> EvalOrder TyName Name PLC.DefaultUni PLC.DefaultFun a
computeEvalOrderCoarse = termEvaluationOrder def mempty

goldenEvalOrder :: String -> TestNested
goldenEvalOrder = goldenPirDoc (prettyPlcReadableDef . computeEvalOrder) pTerm

-- Should hit Unknown before trying to process the undefined. Shows
-- that the computation is lazy
-- [ [ n m ] undefined ]
dangerTerm :: Term TyName Name PLC.DefaultUni PLC.DefaultFun ()
dangerTerm = runQuote $ do
  n <- freshName "n"
  m <- freshName "m"
  pure $ Apply () (Apply () (Var () n) (Var () m)) undefined

evalOrder :: TestNested
evalOrder = testNested "evalOrder"
  [ goldenEvalOrder "letFun"
  , goldenEvalOrder "builtinAppUnsaturated"
  , goldenEvalOrder "builtinAppSaturated"
  , goldenEvalOrder "pureLet"
  , goldenEvalOrder "nestedLets1"
  , pure $ testCase "evalOrderLazy" $ 4 @=? length (unEvalOrder $ computeEvalOrderCoarse dangerTerm)
  ]
