{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}

module Nops where

import           PlutusCore
import           PlutusCore.Constant
import           PlutusCore.Evaluation.Machine.BuiltinCostModel  hiding (BuiltinCostModel)
import           PlutusCore.Evaluation.Machine.MachineParameters
import           PlutusCore.Pretty
import           UntypedPlutusCore.Evaluation.Machine.Cek

import           Control.DeepSeq                                 (NFData)
import           Data.Char                                       (toLower)
import           Data.Ix                                         (Ix)
import           GHC.Generics

data NopBuiltins
    = Nop1
    | Nop2
    | Nop3
    deriving (Show, Eq, Ord, Enum, Bounded, Generic, NFData, Ix, PrettyBy PrettyConfigPlc)

instance Pretty NopBuiltins where
    pretty fun = pretty $ case show fun of
        ""    -> ""
        c : s -> toLower c : s

data NopCostModel =
    NopCostModel
    { paramNop1 :: CostingFun ModelOneArgument
    , paramNop2 :: CostingFun ModelTwoArguments
    , paramNop3 :: CostingFun ModelThreeArguments
    }

-- A fake cost model for nops.  This is just to make sure that the overhead of
-- calling the costing function is included, so the precise contents don't
-- matter as long as the basic form is correct (and benchmarks suggest that nops
-- indeed have constant costs).
nopCostModel :: NopCostModel
nopCostModel =
    NopCostModel
    {
      paramNop1 = CostingFun
                  (ModelOneArgumentConstantCost 120000)
                  (ModelOneArgumentConstantCost 1000)
    , paramNop2 = CostingFun
                  (ModelTwoArgumentsConstantCost 140000)
                  (ModelTwoArgumentsConstantCost 2000)
    , paramNop3 = CostingFun
                  (ModelThreeArgumentsConstantCost 160000)
                  (ModelThreeArgumentsConstantCost 3000)
    }

nopCekParameters :: MachineParameters CekMachineCosts CekValue DefaultUni NopBuiltins
nopCekParameters = toMachineParameters $ CostModel defaultCekMachineCosts nopCostModel

instance uni ~ DefaultUni
    => ToBuiltinMeaning uni NopBuiltins where
        type CostingPart uni NopBuiltins = NopCostModel
        toBuiltinMeaning
            :: forall term . HasConstantIn uni term
               => NopBuiltins -> BuiltinMeaning term NopCostModel
        toBuiltinMeaning Nop1 =
            makeBuiltinMeaning
               @(Integer -> ())
               (\_ -> ())
               (runCostingFunOneArgument . paramNop1)
        toBuiltinMeaning Nop2 =
            makeBuiltinMeaning
               @(Integer -> Integer -> ())
               (\_ _ -> ())
               (runCostingFunTwoArguments . paramNop2)
        toBuiltinMeaning Nop3 =
            makeBuiltinMeaning
               @(Integer -> Integer -> Integer -> ())
               (\_ _ _ -> ())
               (runCostingFunThreeArguments . paramNop3)

