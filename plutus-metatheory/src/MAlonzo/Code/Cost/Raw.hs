{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module MAlonzo.Code.Cost.Raw where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Cost.Base

import Data.SatInt (fromSatInt)
import Data.Functor.Identity (Identity, runIdentity)
import PlutusCore.Evaluation.Machine.ExBudget (ExBudget(..))
import PlutusCore.Evaluation.Machine.ExMemory (ExCPU(..), ExMemory(..))
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCekMachineCostsForTesting)
import UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts (CekMachineCostsBase(..))
import PlutusCore.Evaluation.Machine.CostingFun.SimpleJSON
-- Cost.Raw.HCekMachineCosts
type T_HCekMachineCosts_4 = CekMachineCostsBase Identity
d_HCekMachineCosts_4
  = error
      "MAlonzo Runtime Error: postulate evaluated: Cost.Raw.HCekMachineCosts"
-- Cost.Raw.HExBudget
type T_HExBudget_6 = ExBudget
d_HExBudget_6
  = error
      "MAlonzo Runtime Error: postulate evaluated: Cost.Raw.HExBudget"
-- Cost.Raw.getCekStartupCost
d_getCekStartupCost_8 :: T_HCekMachineCosts_4 -> T_HExBudget_6
d_getCekStartupCost_8 = runIdentity . cekStartupCost
-- Cost.Raw.getCekVarCost
d_getCekVarCost_10 :: T_HCekMachineCosts_4 -> T_HExBudget_6
d_getCekVarCost_10 = runIdentity . cekVarCost
-- Cost.Raw.getCekConstCost
d_getCekConstCost_12 :: T_HCekMachineCosts_4 -> T_HExBudget_6
d_getCekConstCost_12 = runIdentity . cekConstCost
-- Cost.Raw.getCekLamCost
d_getCekLamCost_14 :: T_HCekMachineCosts_4 -> T_HExBudget_6
d_getCekLamCost_14 = runIdentity . cekLamCost
-- Cost.Raw.getCekDelayCost
d_getCekDelayCost_16 :: T_HCekMachineCosts_4 -> T_HExBudget_6
d_getCekDelayCost_16 = runIdentity . cekDelayCost
-- Cost.Raw.getCekForceCost
d_getCekForceCost_18 :: T_HCekMachineCosts_4 -> T_HExBudget_6
d_getCekForceCost_18 = runIdentity . cekForceCost
-- Cost.Raw.getCekApplyCost
d_getCekApplyCost_20 :: T_HCekMachineCosts_4 -> T_HExBudget_6
d_getCekApplyCost_20 = runIdentity . cekApplyCost
-- Cost.Raw.getCekBuiltinCost
d_getCekBuiltinCost_22 :: T_HCekMachineCosts_4 -> T_HExBudget_6
d_getCekBuiltinCost_22 = runIdentity . cekBuiltinCost
-- Cost.Raw.getCekConstrCost
d_getCekConstrCost_24 :: T_HCekMachineCosts_4 -> T_HExBudget_6
d_getCekConstrCost_24 = runIdentity . cekConstrCost
-- Cost.Raw.getCekCaseCost
d_getCekCaseCost_26 :: T_HCekMachineCosts_4 -> T_HExBudget_6
d_getCekCaseCost_26 = runIdentity . cekCaseCost
-- Cost.Raw.getCPUCost
d_getCPUCost_28 :: T_HExBudget_6 -> Integer
d_getCPUCost_28 = fromSatInt . (\(ExCPU x) -> x) . exBudgetCPU
-- Cost.Raw.getMemoryCost
d_getMemoryCost_30 :: T_HExBudget_6 -> Integer
d_getMemoryCost_30
  = fromSatInt . (\(ExMemory x) -> x) . exBudgetMemory
-- Cost.Raw.LinearFunction
d_LinearFunction_32 = ()
type T_LinearFunction_32 = LinearFunction
pattern C_mkLinearFunction_42 a0 a1 = LinearFunction a0 a1
check_mkLinearFunction_42 ::
  Integer -> Integer -> T_LinearFunction_32
check_mkLinearFunction_42 = LinearFunction
cover_LinearFunction_32 :: LinearFunction -> ()
cover_LinearFunction_32 x
  = case x of
      LinearFunction _ _ -> ()
-- Cost.Raw.LinearFunction.intercept
d_intercept_38 :: T_LinearFunction_32 -> Integer
d_intercept_38 v0
  = case coe v0 of
      C_mkLinearFunction_42 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.Raw.LinearFunction.slope
d_slope_40 :: T_LinearFunction_32 -> Integer
d_slope_40 v0
  = case coe v0 of
      C_mkLinearFunction_42 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.Raw.OneVariableQuadraticFunction
d_OneVariableQuadraticFunction_44 = ()
type T_OneVariableQuadraticFunction_44 =
  OneVariableQuadraticFunction
pattern C_mkOneVariableQuadraticFunction_58 a0 a1 a2 = OneVariableQuadraticFunction a0 a1 a2
check_mkOneVariableQuadraticFunction_58 ::
  Integer -> Integer -> Integer -> T_OneVariableQuadraticFunction_44
check_mkOneVariableQuadraticFunction_58
  = OneVariableQuadraticFunction
cover_OneVariableQuadraticFunction_44 ::
  OneVariableQuadraticFunction -> ()
cover_OneVariableQuadraticFunction_44 x
  = case x of
      OneVariableQuadraticFunction _ _ _ -> ()
-- Cost.Raw.OneVariableQuadraticFunction.coeff0
d_coeff0_52 :: T_OneVariableQuadraticFunction_44 -> Integer
d_coeff0_52 v0
  = case coe v0 of
      C_mkOneVariableQuadraticFunction_58 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.Raw.OneVariableQuadraticFunction.coeff1
d_coeff1_54 :: T_OneVariableQuadraticFunction_44 -> Integer
d_coeff1_54 v0
  = case coe v0 of
      C_mkOneVariableQuadraticFunction_58 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.Raw.OneVariableQuadraticFunction.coeff2
d_coeff2_56 :: T_OneVariableQuadraticFunction_44 -> Integer
d_coeff2_56 v0
  = case coe v0 of
      C_mkOneVariableQuadraticFunction_58 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.Raw.TwoVariableLinearFunction
d_TwoVariableLinearFunction_60 = ()
type T_TwoVariableLinearFunction_60 = TwoVariableLinearFunction
pattern C_mkTwoVariableLinearFunction_74 a0 a1 a2 = TwoVariableLinearFunction a0 a1 a2
check_mkTwoVariableLinearFunction_74 ::
  Integer -> Integer -> Integer -> T_TwoVariableLinearFunction_60
check_mkTwoVariableLinearFunction_74 = TwoVariableLinearFunction
cover_TwoVariableLinearFunction_60 ::
  TwoVariableLinearFunction -> ()
cover_TwoVariableLinearFunction_60 x
  = case x of
      TwoVariableLinearFunction _ _ _ -> ()
-- Cost.Raw.TwoVariableLinearFunction.intercept
d_intercept_68 :: T_TwoVariableLinearFunction_60 -> Integer
d_intercept_68 v0
  = case coe v0 of
      C_mkTwoVariableLinearFunction_74 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.Raw.TwoVariableLinearFunction.slope1
d_slope1_70 :: T_TwoVariableLinearFunction_60 -> Integer
d_slope1_70 v0
  = case coe v0 of
      C_mkTwoVariableLinearFunction_74 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.Raw.TwoVariableLinearFunction.slope2
d_slope2_72 :: T_TwoVariableLinearFunction_60 -> Integer
d_slope2_72 v0
  = case coe v0 of
      C_mkTwoVariableLinearFunction_74 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.Raw.TwoVariableQuadraticFunction
d_TwoVariableQuadraticFunction_76 = ()
type T_TwoVariableQuadraticFunction_76 =
  TwoVariableQuadraticFunction
pattern C_mkTwoVariableQuadraticFunction_106 a0 a1 a2 a3 a4 a5 a6 = TwoVariableQuadraticFunction a0 a1 a2 a3 a4 a5 a6
check_mkTwoVariableQuadraticFunction_106 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer -> Integer -> Integer -> T_TwoVariableQuadraticFunction_76
check_mkTwoVariableQuadraticFunction_106
  = TwoVariableQuadraticFunction
cover_TwoVariableQuadraticFunction_76 ::
  TwoVariableQuadraticFunction -> ()
cover_TwoVariableQuadraticFunction_76 x
  = case x of
      TwoVariableQuadraticFunction _ _ _ _ _ _ _ -> ()
-- Cost.Raw.TwoVariableQuadraticFunction.minimum
d_minimum_92 :: T_TwoVariableQuadraticFunction_76 -> Integer
d_minimum_92 v0
  = case coe v0 of
      C_mkTwoVariableQuadraticFunction_106 v1 v2 v3 v4 v5 v6 v7 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.Raw.TwoVariableQuadraticFunction.coeff00
d_coeff00_94 :: T_TwoVariableQuadraticFunction_76 -> Integer
d_coeff00_94 v0
  = case coe v0 of
      C_mkTwoVariableQuadraticFunction_106 v1 v2 v3 v4 v5 v6 v7 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.Raw.TwoVariableQuadraticFunction.coeff10
d_coeff10_96 :: T_TwoVariableQuadraticFunction_76 -> Integer
d_coeff10_96 v0
  = case coe v0 of
      C_mkTwoVariableQuadraticFunction_106 v1 v2 v3 v4 v5 v6 v7 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.Raw.TwoVariableQuadraticFunction.coeff01
d_coeff01_98 :: T_TwoVariableQuadraticFunction_76 -> Integer
d_coeff01_98 v0
  = case coe v0 of
      C_mkTwoVariableQuadraticFunction_106 v1 v2 v3 v4 v5 v6 v7 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.Raw.TwoVariableQuadraticFunction.coeff20
d_coeff20_100 :: T_TwoVariableQuadraticFunction_76 -> Integer
d_coeff20_100 v0
  = case coe v0 of
      C_mkTwoVariableQuadraticFunction_106 v1 v2 v3 v4 v5 v6 v7 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.Raw.TwoVariableQuadraticFunction.coeff11
d_coeff11_102 :: T_TwoVariableQuadraticFunction_76 -> Integer
d_coeff11_102 v0
  = case coe v0 of
      C_mkTwoVariableQuadraticFunction_106 v1 v2 v3 v4 v5 v6 v7 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.Raw.TwoVariableQuadraticFunction.coeff02
d_coeff02_104 :: T_TwoVariableQuadraticFunction_76 -> Integer
d_coeff02_104 v0
  = case coe v0 of
      C_mkTwoVariableQuadraticFunction_106 v1 v2 v3 v4 v5 v6 v7 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.Raw.TwoVariableWithInteractionFunction
d_TwoVariableWithInteractionFunction_108 = ()
type T_TwoVariableWithInteractionFunction_108 =
  TwoVariableWithInteractionFunction
pattern C_mkTwoVariableWithInteractionFunction_126 a0 a1 a2 a3 = TwoVariableWithInteractionFunction a0 a1 a2 a3
check_mkTwoVariableWithInteractionFunction_126 ::
  Integer ->
  Integer ->
  Integer -> Integer -> T_TwoVariableWithInteractionFunction_108
check_mkTwoVariableWithInteractionFunction_126
  = TwoVariableWithInteractionFunction
cover_TwoVariableWithInteractionFunction_108 ::
  TwoVariableWithInteractionFunction -> ()
cover_TwoVariableWithInteractionFunction_108 x
  = case x of
      TwoVariableWithInteractionFunction _ _ _ _ -> ()
-- Cost.Raw.TwoVariableWithInteractionFunction.coeff00'
d_coeff00''_118 ::
  T_TwoVariableWithInteractionFunction_108 -> Integer
d_coeff00''_118 v0
  = case coe v0 of
      C_mkTwoVariableWithInteractionFunction_126 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.Raw.TwoVariableWithInteractionFunction.coeff10'
d_coeff10''_120 ::
  T_TwoVariableWithInteractionFunction_108 -> Integer
d_coeff10''_120 v0
  = case coe v0 of
      C_mkTwoVariableWithInteractionFunction_126 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.Raw.TwoVariableWithInteractionFunction.coeff01'
d_coeff01''_122 ::
  T_TwoVariableWithInteractionFunction_108 -> Integer
d_coeff01''_122 v0
  = case coe v0 of
      C_mkTwoVariableWithInteractionFunction_126 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.Raw.TwoVariableWithInteractionFunction.coeff11'
d_coeff11''_124 ::
  T_TwoVariableWithInteractionFunction_108 -> Integer
d_coeff11''_124 v0
  = case coe v0 of
      C_mkTwoVariableWithInteractionFunction_126 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.Raw.ExpModCostingFunction
d_ExpModCostingFunction_128 = ()
type T_ExpModCostingFunction_128 = ExpModCostingFunction
pattern C_mkExpModCostingFunction_142 a0 a1 a2 = ExpModCostingFunction a0 a1 a2
check_mkExpModCostingFunction_142 ::
  Integer -> Integer -> Integer -> T_ExpModCostingFunction_128
check_mkExpModCostingFunction_142 = ExpModCostingFunction
cover_ExpModCostingFunction_128 :: ExpModCostingFunction -> ()
cover_ExpModCostingFunction_128 x
  = case x of
      ExpModCostingFunction _ _ _ -> ()
-- Cost.Raw.ExpModCostingFunction.coeff00
d_coeff00_136 :: T_ExpModCostingFunction_128 -> Integer
d_coeff00_136 v0
  = case coe v0 of
      C_mkExpModCostingFunction_142 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.Raw.ExpModCostingFunction.coeff11
d_coeff11_138 :: T_ExpModCostingFunction_128 -> Integer
d_coeff11_138 v0
  = case coe v0 of
      C_mkExpModCostingFunction_142 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.Raw.ExpModCostingFunction.coeff12
d_coeff12_140 :: T_ExpModCostingFunction_128 -> Integer
d_coeff12_140 v0
  = case coe v0 of
      C_mkExpModCostingFunction_142 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.Raw.RawModel
d_RawModel_144 = ()
type T_RawModel_144 = Model
pattern C_ConstantCost_146 a0 = ConstantCost a0
pattern C_AddedSizes_148 a0 = AddedSizes a0
pattern C_MultipliedSizes_150 a0 = MultipliedSizes a0
pattern C_MinSize_152 a0 = MinSize a0
pattern C_MaxSize_154 a0 = MaxSize a0
pattern C_LinearInX_156 a0 = LinearInX a0
pattern C_LinearInY_158 a0 = LinearInY a0
pattern C_LinearInZ_160 a0 = LinearInZ a0
pattern C_LinearInU_162 a0 = LinearInU a0
pattern C_LiteralInYOrLinearInZ_164 a0 = LiteralInYOrLinearInZ a0
pattern C_LinearInMaxYZ_166 a0 = LinearInMaxYZ a0
pattern C_LinearInXAndY_168 a0 = LinearInXAndY a0
pattern C_LinearInYAndZ_170 a0 = LinearInYAndZ a0
pattern C_QuadraticInX_172 a0 = QuadraticInX a0
pattern C_QuadraticInY_174 a0 = QuadraticInY a0
pattern C_QuadraticInZ_176 a0 = QuadraticInZ a0
pattern C_QuadraticInXAndY_178 a0 = QuadraticInXAndY a0
pattern C_WithInteractionInXAndY_180 a0 = WithInteractionInXAndY a0
pattern C_SubtractedSizes_182 a0 a1 = SubtractedSizes a0 a1
pattern C_ConstAboveDiagonal_184 a0 a1 = ConstAboveDiagonal a0 a1
pattern C_ConstBelowDiagonal_186 a0 a1 = ConstBelowDiagonal a0 a1
pattern C_ConstOffDiagonal_188 a0 a1 = ConstOffDiagonal a0 a1
pattern C_ExpModCost_190 a0 = ExpModCost a0
check_ConstantCost_146 :: Integer -> T_RawModel_144
check_ConstantCost_146 = ConstantCost
check_AddedSizes_148 :: T_LinearFunction_32 -> T_RawModel_144
check_AddedSizes_148 = AddedSizes
check_MultipliedSizes_150 :: T_LinearFunction_32 -> T_RawModel_144
check_MultipliedSizes_150 = MultipliedSizes
check_MinSize_152 :: T_LinearFunction_32 -> T_RawModel_144
check_MinSize_152 = MinSize
check_MaxSize_154 :: T_LinearFunction_32 -> T_RawModel_144
check_MaxSize_154 = MaxSize
check_LinearInX_156 :: T_LinearFunction_32 -> T_RawModel_144
check_LinearInX_156 = LinearInX
check_LinearInY_158 :: T_LinearFunction_32 -> T_RawModel_144
check_LinearInY_158 = LinearInY
check_LinearInZ_160 :: T_LinearFunction_32 -> T_RawModel_144
check_LinearInZ_160 = LinearInZ
check_LinearInU_162 :: T_LinearFunction_32 -> T_RawModel_144
check_LinearInU_162 = LinearInU
check_LiteralInYOrLinearInZ_164 ::
  T_LinearFunction_32 -> T_RawModel_144
check_LiteralInYOrLinearInZ_164 = LiteralInYOrLinearInZ
check_LinearInMaxYZ_166 :: T_LinearFunction_32 -> T_RawModel_144
check_LinearInMaxYZ_166 = LinearInMaxYZ
check_LinearInXAndY_168 ::
  T_TwoVariableLinearFunction_60 -> T_RawModel_144
check_LinearInXAndY_168 = LinearInXAndY
check_LinearInYAndZ_170 ::
  T_TwoVariableLinearFunction_60 -> T_RawModel_144
check_LinearInYAndZ_170 = LinearInYAndZ
check_QuadraticInX_172 ::
  T_OneVariableQuadraticFunction_44 -> T_RawModel_144
check_QuadraticInX_172 = QuadraticInX
check_QuadraticInY_174 ::
  T_OneVariableQuadraticFunction_44 -> T_RawModel_144
check_QuadraticInY_174 = QuadraticInY
check_QuadraticInZ_176 ::
  T_OneVariableQuadraticFunction_44 -> T_RawModel_144
check_QuadraticInZ_176 = QuadraticInZ
check_QuadraticInXAndY_178 ::
  T_TwoVariableQuadraticFunction_76 -> T_RawModel_144
check_QuadraticInXAndY_178 = QuadraticInXAndY
check_WithInteractionInXAndY_180 ::
  T_TwoVariableWithInteractionFunction_108 -> T_RawModel_144
check_WithInteractionInXAndY_180 = WithInteractionInXAndY
check_SubtractedSizes_182 ::
  T_LinearFunction_32 -> Integer -> T_RawModel_144
check_SubtractedSizes_182 = SubtractedSizes
check_ConstAboveDiagonal_184 ::
  Integer -> T_RawModel_144 -> T_RawModel_144
check_ConstAboveDiagonal_184 = ConstAboveDiagonal
check_ConstBelowDiagonal_186 ::
  Integer -> T_RawModel_144 -> T_RawModel_144
check_ConstBelowDiagonal_186 = ConstBelowDiagonal
check_ConstOffDiagonal_188 ::
  Integer -> T_RawModel_144 -> T_RawModel_144
check_ConstOffDiagonal_188 = ConstOffDiagonal
check_ExpModCost_190 ::
  T_ExpModCostingFunction_128 -> T_RawModel_144
check_ExpModCost_190 = ExpModCost
cover_RawModel_144 :: Model -> ()
cover_RawModel_144 x
  = case x of
      ConstantCost _ -> ()
      AddedSizes _ -> ()
      MultipliedSizes _ -> ()
      MinSize _ -> ()
      MaxSize _ -> ()
      LinearInX _ -> ()
      LinearInY _ -> ()
      LinearInZ _ -> ()
      LinearInU _ -> ()
      LiteralInYOrLinearInZ _ -> ()
      LinearInMaxYZ _ -> ()
      LinearInXAndY _ -> ()
      LinearInYAndZ _ -> ()
      QuadraticInX _ -> ()
      QuadraticInY _ -> ()
      QuadraticInZ _ -> ()
      QuadraticInXAndY _ -> ()
      WithInteractionInXAndY _ -> ()
      SubtractedSizes _ _ -> ()
      ConstAboveDiagonal _ _ -> ()
      ConstBelowDiagonal _ _ -> ()
      ConstOffDiagonal _ _ -> ()
      ExpModCost _ -> ()
-- Cost.Raw.CpuAndMemoryModel
d_CpuAndMemoryModel_192 = ()
type T_CpuAndMemoryModel_192 = CpuAndMemoryModel
pattern C_mkCpuAndMemoryModel_202 a0 a1 = CpuAndMemoryModel a0 a1
check_mkCpuAndMemoryModel_202 ::
  T_RawModel_144 -> T_RawModel_144 -> T_CpuAndMemoryModel_192
check_mkCpuAndMemoryModel_202 = CpuAndMemoryModel
cover_CpuAndMemoryModel_192 :: CpuAndMemoryModel -> ()
cover_CpuAndMemoryModel_192 x
  = case x of
      CpuAndMemoryModel _ _ -> ()
-- Cost.Raw.CpuAndMemoryModel.cpuModel
d_cpuModel_198 :: T_CpuAndMemoryModel_192 -> T_RawModel_144
d_cpuModel_198 v0
  = case coe v0 of
      C_mkCpuAndMemoryModel_202 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.Raw.CpuAndMemoryModel.memoryModel
d_memoryModel_200 :: T_CpuAndMemoryModel_192 -> T_RawModel_144
d_memoryModel_200 v0
  = case coe v0 of
      C_mkCpuAndMemoryModel_202 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.Raw.BuiltinCostMap
d_BuiltinCostMap_204 :: ()
d_BuiltinCostMap_204 = erased
-- Cost.Raw.RawCostModel
d_RawCostModel_206 :: ()
d_RawCostModel_206 = erased
