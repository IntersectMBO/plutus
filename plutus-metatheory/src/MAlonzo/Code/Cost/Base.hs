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

module MAlonzo.Code.Cost.Base where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Builtin
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.Vec.Base

-- Cost.Base.CostingNat
d_CostingNat_4 :: ()
d_CostingNat_4 = erased
-- Cost.Base.StepKind
d_StepKind_6 = ()
data T_StepKind_6
  = C_BConst_8 | C_BVar_10 | C_BLamAbs_12 | C_BApply_14 |
    C_BDelay_16 | C_BForce_18 | C_BBuiltin_20 | C_BConstr_22 |
    C_BCase_24
-- Cost.Base.showStepKind'
d_showStepKind''_26 ::
  T_StepKind_6 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showStepKind''_26 v0
  = case coe v0 of
      C_BConst_8 -> coe ("BConst" :: Data.Text.Text)
      C_BVar_10 -> coe ("BVar" :: Data.Text.Text)
      C_BLamAbs_12 -> coe ("BLamAbs" :: Data.Text.Text)
      C_BApply_14 -> coe ("BApply" :: Data.Text.Text)
      C_BDelay_16 -> coe ("BDelay" :: Data.Text.Text)
      C_BForce_18 -> coe ("BForce" :: Data.Text.Text)
      C_BBuiltin_20 -> coe ("BBuiltin" :: Data.Text.Text)
      C_BConstr_22 -> coe ("BConstr" :: Data.Text.Text)
      C_BCase_24 -> coe ("BCase" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.Base.showStepKind
d_showStepKind_28 ::
  T_StepKind_6 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showStepKind_28 v0
  = coe
      MAlonzo.Code.Data.Maybe.Base.du_fromMaybe_46 ("" :: Data.Text.Text)
      (coe
         MAlonzo.Code.Data.String.Base.d_tail_14
         (d_showStepKind''_26 (coe v0)))
-- Cost.Base.stepKindList
d_stepKindList_32 :: [T_StepKind_6]
d_stepKindList_32
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe C_BConst_8)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe C_BVar_10)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe C_BLamAbs_12)
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe C_BApply_14)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe C_BDelay_16)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe C_BForce_18)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe C_BBuiltin_20)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe C_BConstr_22)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe C_BCase_24)
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))
-- Cost.Base.ExBudgetCategory
d_ExBudgetCategory_34 = ()
data T_ExBudgetCategory_34
  = C_BStep_36 T_StepKind_6 |
    C_BBuiltinApp_40 MAlonzo.Code.Builtin.T_Builtin_2
                     MAlonzo.Code.Data.Vec.Base.T_Vec_28 |
    C_BStartup_42
-- Cost.Base.MachineParameters
d_MachineParameters_46 a0 = ()
data T_MachineParameters_46
  = C_MachineParameters'46'constructor_359 (T_ExBudgetCategory_34 ->
                                            AgdaAny)
                                           AgdaAny (AgdaAny -> AgdaAny -> AgdaAny)
                                           MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
-- Cost.Base.MachineParameters.cekMachineCost
d_cekMachineCost_58 ::
  T_MachineParameters_46 -> T_ExBudgetCategory_34 -> AgdaAny
d_cekMachineCost_58 v0
  = case coe v0 of
      C_MachineParameters'46'constructor_359 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.Base.MachineParameters.ε
d_ε_60 :: T_MachineParameters_46 -> AgdaAny
d_ε_60 v0
  = case coe v0 of
      C_MachineParameters'46'constructor_359 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.Base.MachineParameters._∙_
d__'8729'__62 ::
  T_MachineParameters_46 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8729'__62 v0
  = case coe v0 of
      C_MachineParameters'46'constructor_359 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.Base.MachineParameters.costMonoid
d_costMonoid_64 ::
  T_MachineParameters_46 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_costMonoid_64 v0
  = case coe v0 of
      C_MachineParameters'46'constructor_359 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.Base.MachineParameters.startupCost
d_startupCost_66 :: () -> T_MachineParameters_46 -> AgdaAny
d_startupCost_66 ~v0 v1 = du_startupCost_66 v1
du_startupCost_66 :: T_MachineParameters_46 -> AgdaAny
du_startupCost_66 v0
  = coe d_cekMachineCost_58 v0 (coe C_BStartup_42)
