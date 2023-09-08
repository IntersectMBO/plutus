{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
module AnalysisSpec where

import Test.Tasty.Extras

import Algebra.Graph qualified as G
import Control.Lens
import Data.Map qualified as Map
import PlutusCore qualified as PLC
import PlutusCore.Name qualified as PLC
import PlutusCore.Pretty (prettyPlcReadableDef)
import PlutusCore.Quote
import PlutusIR
import PlutusIR.Analysis.Dependencies
import PlutusIR.Analysis.Dependencies qualified as Deps
import PlutusIR.Parser
import PlutusIR.Purity
import PlutusIR.Test
import PlutusIR.Transform.Rename ()
import PlutusPrelude (def)
import Test.Tasty.HUnit

computeEvalOrder
  :: Term TyName Name PLC.DefaultUni PLC.DefaultFun a
  -> EvalOrder TyName Name PLC.DefaultUni PLC.DefaultFun a
computeEvalOrder tm =
  let
    semvar = def
    varStrictMap = snd $ runTermDeps @(G.Graph Deps.Node) semvar tm
    variableStrictness :: Name -> Strictness
    variableStrictness n = Map.findWithDefault NonStrict (n ^. PLC.theUnique) varStrictMap
  in termEvaluationOrder semvar variableStrictness tm

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
  , pure $ testCase "evalOrderLazy" $ 4 @=? length (unEvalOrder $ computeEvalOrder dangerTerm)
  ]
