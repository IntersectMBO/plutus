{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

{- | A set of no-op built-in functions used in cost model calibration. Benchmarks
   based on these are used to estimate the overhead of calling a built-in
   function.
-}

module Nops (NopFuns(..), nopCostParameters) where

import           PlutusCore
import           PlutusCore.Constant
import           PlutusCore.Evaluation.Machine.BuiltinCostModel  hiding (BuiltinCostModel)
import           PlutusCore.Evaluation.Machine.MachineParameters
import           PlutusCore.Pretty
import           UntypedPlutusCore.Evaluation.Machine.Cek

import           Control.DeepSeq                                 (NFData)
import           Data.Char                                       (toLower)
import           Data.Ix                                         (Ix)
import           GHC.Generics                                    (Generic)

data NopFuns
    = Nop1
    | Nop2
    | Nop3
    deriving (Show, Eq, Ord, Enum, Bounded, Generic, NFData, Ix, PrettyBy PrettyConfigPlc)

instance Pretty NopFuns where
    pretty fun = pretty $ case show fun of
        ""    -> ""
        c : s -> toLower c : s

data NopCostModel =
    NopCostModel
    { paramNop1 :: CostingFun ModelOneArgument
    , paramNop2 :: CostingFun ModelTwoArguments
    , paramNop3 :: CostingFun ModelThreeArguments
    }

{- | A fake cost model for nops.  This is just to make sure that the overhead of
   calling the costing function is included, so the precise contents don't
   matter as long as the basic form is correct (and benchmarks suggest that nops
   indeed have constant costs). -}
nopCostModel :: NopCostModel
nopCostModel =
    NopCostModel
    {
      paramNop1 = CostingFun
                  (ModelOneArgumentConstantCost 1000000)
                  (ModelOneArgumentConstantCost 100)
    , paramNop2 = CostingFun
                  (ModelTwoArgumentsConstantCost 1200000)
                  (ModelTwoArgumentsConstantCost 200)
    , paramNop3 = CostingFun
                  (ModelThreeArgumentsConstantCost 1500000)
                  (ModelThreeArgumentsConstantCost 300)
    }

nopCostParameters :: MachineParameters CekMachineCosts CekValue DefaultUni NopFuns
nopCostParameters = toMachineParameters $ CostModel defaultCekMachineCosts nopCostModel

{- | The meanings of the builtins.  Each one takes a number of integer arguments
   and returns an integer without doing any other work.  We could have used
   units instead of integers, but using integers makes it possible to check that
   the cost of calling the functions doesn't depend on the size of the
   arguments.  We have checked this and there there was no dependence: let's
   leave open the possibility of doing it again in case anything changes.
-}
instance (uni `Contains` Integer, GEq uni, GShow uni) => ToBuiltinMeaning uni NopFuns where
    type CostingPart uni NopFuns = NopCostModel
    toBuiltinMeaning
        :: HasConstantIn uni term
           => NopFuns -> BuiltinMeaning term NopCostModel
    toBuiltinMeaning Nop1 =
        makeBuiltinMeaning
             @(Integer -> Integer)
             (\_ -> 11)
             (runCostingFunOneArgument . paramNop1)
    toBuiltinMeaning Nop2 =
        makeBuiltinMeaning
             @(Integer -> Integer -> Integer)
             (\_ _ -> 22)
             (runCostingFunTwoArguments . paramNop2)
    toBuiltinMeaning Nop3 =
        makeBuiltinMeaning
             @(Integer -> Integer -> Integer -> Integer)
             (\_ _ _ -> 33)
             (runCostingFunThreeArguments . paramNop3)

