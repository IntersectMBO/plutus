{-# LANGUAGE TypeApplications #-}
module AnalysisSpec where

import Test.Tasty.Extras

import Algebra.Graph qualified as G
import Control.Lens
import Data.Map qualified as Map
import PlutusCore qualified as PLC
import PlutusCore.Name qualified as PLC
import PlutusCore.Pretty (prettyPlcReadableDef)
import PlutusIR
import PlutusIR.Analysis.Dependencies
import PlutusIR.Analysis.Dependencies qualified as Deps
import PlutusIR.Parser
import PlutusIR.Purity
import PlutusIR.Test
import PlutusIR.Transform.Rename ()
import PlutusPrelude (def)

goldenEvalOrder :: String -> TestNested
goldenEvalOrder name =
  let
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
  in goldenPirDoc (prettyPlcReadableDef . computeEvalOrder) pTerm name

evalOrder :: TestNested
evalOrder = testNested "evalOrder"
  [ goldenEvalOrder "letFun"
  , goldenEvalOrder "builtinAppUnsaturated"
  , goldenEvalOrder "builtinAppSaturated"
  , goldenEvalOrder "pureLet"
  , goldenEvalOrder "nestedLets1"
  ]
