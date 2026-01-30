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

module MAlonzo.Code.Cost where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Float
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Builtin
import qualified MAlonzo.Code.Builtin.Constant.AtomicType
import qualified MAlonzo.Code.Builtin.Signature
import qualified MAlonzo.Code.Cost.Base
import qualified MAlonzo.Code.Cost.Model
import qualified MAlonzo.Code.Cost.Raw
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Tree.AVL
import qualified MAlonzo.Code.Data.Tree.AVL.Map
import qualified MAlonzo.Code.Data.Tree.AVL.Value
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Text.Printf
import qualified MAlonzo.Code.Untyped.CEK
import qualified MAlonzo.Code.Utils

-- Cost.AVL.Map
d_Map_6 :: MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()
d_Map_6 = erased
-- Cost.ExBudget
d_ExBudget_52 = ()
data T_ExBudget_52 = C_mkExBudget_62 Integer Integer
-- Cost.ExBudget.ExCPU
d_ExCPU_58 :: T_ExBudget_52 -> Integer
d_ExCPU_58 v0
  = case coe v0 of
      C_mkExBudget_62 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.ExBudget.ExMem
d_ExMem_60 :: T_ExBudget_52 -> Integer
d_ExMem_60 v0
  = case coe v0 of
      C_mkExBudget_62 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.fromHExBudget
d_fromHExBudget_64 ::
  MAlonzo.Code.Cost.Raw.T_HExBudget_6 -> T_ExBudget_52
d_fromHExBudget_64 v0
  = coe
      C_mkExBudget_62 (coe MAlonzo.Code.Cost.Raw.d_getCPUCost_28 v0)
      (coe MAlonzo.Code.Cost.Raw.d_getMemoryCost_30 v0)
-- Cost.ε€
d_ε'8364'_68 :: T_ExBudget_52
d_ε'8364'_68
  = coe C_mkExBudget_62 (coe (0 :: Integer)) (coe (0 :: Integer))
-- Cost._∙€_
d__'8729''8364'__70 ::
  T_ExBudget_52 -> T_ExBudget_52 -> T_ExBudget_52
d__'8729''8364'__70 v0 v1
  = case coe v0 of
      C_mkExBudget_62 v2 v3
        -> case coe v1 of
             C_mkExBudget_62 v4 v5
               -> coe
                    C_mkExBudget_62 (coe addInt (coe v2) (coe v4))
                    (coe addInt (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.isMonoidExBudget
d_isMonoidExBudget_80 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoidExBudget_80
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMonoid'46'constructor_15873
      (coe
         MAlonzo.Code.Algebra.Structures.C_IsSemigroup'46'constructor_10417
         (coe
            MAlonzo.Code.Algebra.Structures.C_IsMagma'46'constructor_1867
            (coe
               MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
            erased)
         erased)
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
-- Cost.builtinCost
d_builtinCost_96 ::
  MAlonzo.Code.Builtin.T_Builtin_2 ->
  MAlonzo.Code.Cost.Model.T_BuiltinModel_62 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> T_ExBudget_52
d_builtinCost_96 v0 v1 v2
  = coe
      C_mkExBudget_62
      (coe
         MAlonzo.Code.Cost.Model.d_runModel_96
         (coe MAlonzo.Code.Builtin.d_arity_304 (coe v0))
         (coe MAlonzo.Code.Cost.Model.d_costingCPU_70 (coe v1)) (coe v2))
      (coe
         MAlonzo.Code.Cost.Model.d_runModel_96
         (coe MAlonzo.Code.Builtin.d_arity_304 (coe v0))
         (coe MAlonzo.Code.Cost.Model.d_costingMem_72 (coe v1)) (coe v2))
-- Cost.CostModel
d_CostModel_104 :: ()
d_CostModel_104 = erased
-- Cost.cekMachineCostFunction
d_cekMachineCostFunction_106 ::
  MAlonzo.Code.Cost.Raw.T_HCekMachineCosts_4 ->
  MAlonzo.Code.Cost.Base.T_StepKind_6 -> T_ExBudget_52
d_cekMachineCostFunction_106 v0 v1
  = case coe v1 of
      MAlonzo.Code.Cost.Base.C_BConst_8
        -> coe
             d_fromHExBudget_64
             (coe MAlonzo.Code.Cost.Raw.d_getCekConstCost_12 v0)
      MAlonzo.Code.Cost.Base.C_BVar_10
        -> coe
             d_fromHExBudget_64
             (coe MAlonzo.Code.Cost.Raw.d_getCekVarCost_10 v0)
      MAlonzo.Code.Cost.Base.C_BLamAbs_12
        -> coe
             d_fromHExBudget_64
             (coe MAlonzo.Code.Cost.Raw.d_getCekLamCost_14 v0)
      MAlonzo.Code.Cost.Base.C_BApply_14
        -> coe
             d_fromHExBudget_64
             (coe MAlonzo.Code.Cost.Raw.d_getCekApplyCost_20 v0)
      MAlonzo.Code.Cost.Base.C_BDelay_16
        -> coe
             d_fromHExBudget_64
             (coe MAlonzo.Code.Cost.Raw.d_getCekDelayCost_16 v0)
      MAlonzo.Code.Cost.Base.C_BForce_18
        -> coe
             d_fromHExBudget_64
             (coe MAlonzo.Code.Cost.Raw.d_getCekForceCost_18 v0)
      MAlonzo.Code.Cost.Base.C_BBuiltin_20
        -> coe
             d_fromHExBudget_64
             (coe MAlonzo.Code.Cost.Raw.d_getCekBuiltinCost_22 v0)
      MAlonzo.Code.Cost.Base.C_BConstr_22
        -> coe
             d_fromHExBudget_64
             (coe MAlonzo.Code.Cost.Raw.d_getCekConstCost_12 v0)
      MAlonzo.Code.Cost.Base.C_BCase_24
        -> coe
             d_fromHExBudget_64
             (coe MAlonzo.Code.Cost.Raw.d_getCekCaseCost_26 v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.exBudgetCategoryCost
d_exBudgetCategoryCost_126 ::
  MAlonzo.Code.Utils.T__'215'__396
    MAlonzo.Code.Cost.Raw.T_HCekMachineCosts_4
    (MAlonzo.Code.Builtin.T_Builtin_2 ->
     MAlonzo.Code.Cost.Model.T_BuiltinModel_62) ->
  MAlonzo.Code.Cost.Base.T_ExBudgetCategory_34 -> T_ExBudget_52
d_exBudgetCategoryCost_126 v0 v1
  = case coe v0 of
      MAlonzo.Code.Utils.C__'44'__410 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Cost.Base.C_BStep_36 v4
               -> coe d_cekMachineCostFunction_106 (coe v2) (coe v4)
             MAlonzo.Code.Cost.Base.C_BBuiltinApp_40 v4 v5
               -> coe d_builtinCost_96 (coe v4) (coe v3 v4) (coe v5)
             MAlonzo.Code.Cost.Base.C_BStartup_42
               -> coe
                    d_fromHExBudget_64
                    (coe MAlonzo.Code.Cost.Raw.d_getCekStartupCost_8 v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.machineParameters
d_machineParameters_140 ::
  MAlonzo.Code.Utils.T__'215'__396
    MAlonzo.Code.Cost.Raw.T_HCekMachineCosts_4
    (MAlonzo.Code.Builtin.T_Builtin_2 ->
     MAlonzo.Code.Cost.Model.T_BuiltinModel_62) ->
  MAlonzo.Code.Cost.Base.T_MachineParameters_46
d_machineParameters_140 v0
  = coe
      MAlonzo.Code.Cost.Base.C_MachineParameters'46'constructor_359
      (coe d_exBudgetCategoryCost_126 (coe v0)) (coe d_ε'8364'_68)
      (coe d__'8729''8364'__70) (coe d_isMonoidExBudget_80)
-- Cost.countingReport
d_countingReport_144 ::
  T_ExBudget_52 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_countingReport_144 v0
  = case coe v0 of
      C_mkExBudget_62 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("\nCPU budget:    " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("\nMemory budget: " :: Data.Text.Text)
                   (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.mkKeyFromExBudgetCategory
d_mkKeyFromExBudgetCategory_150 ::
  MAlonzo.Code.Cost.Base.T_ExBudgetCategory_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_mkKeyFromExBudgetCategory_150 v0
  = case coe v0 of
      MAlonzo.Code.Cost.Base.C_BStep_36 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("0" :: Data.Text.Text)
             (MAlonzo.Code.Cost.Base.d_showStepKind_28 (coe v1))
      MAlonzo.Code.Cost.Base.C_BBuiltinApp_40 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("1" :: Data.Text.Text)
             (MAlonzo.Code.Builtin.d_showBuiltin_428 (coe v1))
      MAlonzo.Code.Cost.Base.C_BStartup_42 -> coe ("2" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.TallyingBudget
d_TallyingBudget_156 :: ()
d_TallyingBudget_156 = erased
-- Cost.lookup
d_lookup_158 ::
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Cost.Base.T_ExBudgetCategory_34 -> T_ExBudget_52
d_lookup_158 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Data.Tree.AVL.du_lookup_312
              (coe
                 MAlonzo.Code.Data.String.Properties.d_'60''45'strictTotalOrder'45''8776'_76)
              (coe MAlonzo.Code.Data.Tree.AVL.Value.du_const_94) (coe v0)
              (coe d_mkKeyFromExBudgetCategory_150 (coe v1)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3 -> coe v3
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe d_ε'8364'_68
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Cost.εT
d_εT_178 ::
  MAlonzo.Code.Utils.T__'215'__396
    MAlonzo.Code.Data.Tree.AVL.T_Tree_254 T_ExBudget_52
d_εT_178
  = coe
      MAlonzo.Code.Utils.C__'44'__410
      (coe MAlonzo.Code.Data.Tree.AVL.Map.du_empty_198)
      (coe d_ε'8364'_68)
-- Cost._∙T_
d__'8729'T__180 ::
  MAlonzo.Code.Utils.T__'215'__396
    MAlonzo.Code.Data.Tree.AVL.T_Tree_254 T_ExBudget_52 ->
  MAlonzo.Code.Utils.T__'215'__396
    MAlonzo.Code.Data.Tree.AVL.T_Tree_254 T_ExBudget_52 ->
  MAlonzo.Code.Utils.T__'215'__396
    MAlonzo.Code.Data.Tree.AVL.T_Tree_254 T_ExBudget_52
d__'8729'T__180 v0 v1
  = case coe v0 of
      MAlonzo.Code.Utils.C__'44'__410 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Utils.C__'44'__410 v4 v5
               -> coe
                    MAlonzo.Code.Utils.C__'44'__410
                    (coe
                       MAlonzo.Code.Data.Tree.AVL.Map.du_unionWith_232
                       MAlonzo.Code.Data.String.Properties.d_'60''45'strictTotalOrder'45''8776'_76
                       (coe du_u_194) v2 v4)
                    (coe d__'8729''8364'__70 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost._.u
d_u_194 ::
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  T_ExBudget_52 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  T_ExBudget_52 ->
  T_ExBudget_52 -> Maybe T_ExBudget_52 -> T_ExBudget_52
d_u_194 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_u_194 v4 v5
du_u_194 :: T_ExBudget_52 -> Maybe T_ExBudget_52 -> T_ExBudget_52
du_u_194 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe d__'8729''8364'__70 (coe v0) (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.TallyingBudget-assoc
d_TallyingBudget'45'assoc_202
  = error
      "MAlonzo Runtime Error: postulate evaluated: Cost.TallyingBudget-assoc"
-- Cost.Tallying-budget-identityʳ
d_Tallying'45'budget'45'identity'691'_204
  = error
      "MAlonzo Runtime Error: postulate evaluated: Cost.Tallying-budget-identity\691"
-- Cost.isMonoidTallyingBudget
d_isMonoidTallyingBudget_206 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoidTallyingBudget_206
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMonoid'46'constructor_15873
      (coe
         MAlonzo.Code.Algebra.Structures.C_IsSemigroup'46'constructor_10417
         (coe
            MAlonzo.Code.Algebra.Structures.C_IsMagma'46'constructor_1867
            (coe
               MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
            erased)
         erased)
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
-- Cost.tallyingCekMachineCost
d_tallyingCekMachineCost_212 ::
  MAlonzo.Code.Utils.T__'215'__396
    MAlonzo.Code.Cost.Raw.T_HCekMachineCosts_4
    (MAlonzo.Code.Builtin.T_Builtin_2 ->
     MAlonzo.Code.Cost.Model.T_BuiltinModel_62) ->
  MAlonzo.Code.Cost.Base.T_ExBudgetCategory_34 ->
  MAlonzo.Code.Utils.T__'215'__396
    MAlonzo.Code.Data.Tree.AVL.T_Tree_254 T_ExBudget_52
d_tallyingCekMachineCost_212 v0 v1
  = coe
      MAlonzo.Code.Utils.C__'44'__410
      (coe
         MAlonzo.Code.Data.Tree.AVL.Map.du_singleton_200
         (d_mkKeyFromExBudgetCategory_150 (coe v1))
         (d_exBudgetCategoryCost_126 (coe v0) (coe v1)))
      (coe d_exBudgetCategoryCost_126 (coe v0) (coe v1))
-- Cost.tallyingMachineParameters
d_tallyingMachineParameters_220 ::
  MAlonzo.Code.Utils.T__'215'__396
    MAlonzo.Code.Cost.Raw.T_HCekMachineCosts_4
    (MAlonzo.Code.Builtin.T_Builtin_2 ->
     MAlonzo.Code.Cost.Model.T_BuiltinModel_62) ->
  MAlonzo.Code.Cost.Base.T_MachineParameters_46
d_tallyingMachineParameters_220 v0
  = coe
      MAlonzo.Code.Cost.Base.C_MachineParameters'46'constructor_359
      (coe d_tallyingCekMachineCost_212 (coe v0)) (coe d_εT_178)
      (coe d__'8729'T__180) (coe d_isMonoidTallyingBudget_206)
-- Cost.tallyingReport
d_tallyingReport_224 ::
  MAlonzo.Code.Utils.T__'215'__396
    MAlonzo.Code.Data.Tree.AVL.T_Tree_254 T_ExBudget_52 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_tallyingReport_224 v0
  = case coe v0 of
      MAlonzo.Code.Utils.C__'44'__410 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (d_countingReport_144 (coe v2))
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("\n" :: Data.Text.Text)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("\n" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (coe du_printStepReport_260 (coe v1))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("\n" :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            ("startup    " :: Data.Text.Text)
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               (coe
                                  du_budgetToString_248
                                  (coe
                                     d_lookup_158 (coe v1)
                                     (coe MAlonzo.Code.Cost.Base.C_BStartup_42)))
                               (coe
                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                  ("\n" :: Data.Text.Text)
                                  (coe
                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                     ("compute    " :: Data.Text.Text)
                                     (coe
                                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                        (coe
                                           du_budgetToString_248
                                           (coe du_totalComputeCost_234 (coe v1)))
                                        (coe
                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                           ("\n" :: Data.Text.Text)
                                           (coe
                                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                              ("\n\n" :: Data.Text.Text)
                                              (coe
                                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                 (coe du_printBuiltinReport_276 (coe v1))
                                                 (coe
                                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                    ("\n" :: Data.Text.Text)
                                                    (coe
                                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                       ("Total builtin costs:   " :: Data.Text.Text)
                                                       (coe
                                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                          (coe
                                                             du_budgetToString_248
                                                             (coe
                                                                du_totalBuiltinCosts_236 (coe v1)))
                                                          (coe
                                                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                             ("\n" :: Data.Text.Text)
                                                             (coe
                                                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                (coe
                                                                   MAlonzo.Code.Text.Printf.d_printf_24
                                                                   ("Time spent executing builtins:  %f%%\n"
                                                                    ::
                                                                    Data.Text.Text)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Float.d_primFloatDiv_54
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Float.d_primFloatTimes_52
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Float.d_primNatToFloat_24
                                                                            (100 :: Integer))
                                                                         (coe
                                                                            du_getCPU_244
                                                                            (coe
                                                                               du_totalBuiltinCosts_236
                                                                               (coe v1))))
                                                                      (coe du_getCPU_244 (coe v2))))
                                                                (coe
                                                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                   ("\n" :: Data.Text.Text)
                                                                   (coe
                                                                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                      ("\n" :: Data.Text.Text)
                                                                      (coe
                                                                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                         ("Total budget spent:    "
                                                                          ::
                                                                          Data.Text.Text)
                                                                         (coe
                                                                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                            (coe
                                                                               du_budgetToString_248
                                                                               (coe v2))
                                                                            (coe
                                                                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                               ("\n"
                                                                                ::
                                                                                Data.Text.Text)
                                                                               (coe
                                                                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                                  ("Predicted execution time: "
                                                                                   ::
                                                                                   Data.Text.Text)
                                                                                  (coe
                                                                                     du_formatTimePicoseconds_284
                                                                                     (coe
                                                                                        du_getCPU_244
                                                                                        (coe
                                                                                           v2))))))))))))))))))))))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost._.totalComputeCost
d_totalComputeCost_234 ::
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  T_ExBudget_52 -> T_ExBudget_52
d_totalComputeCost_234 v0 ~v1 = du_totalComputeCost_234 v0
du_totalComputeCost_234 ::
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 -> T_ExBudget_52
du_totalComputeCost_234 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216
      (coe
         (\ v1 ->
            d__'8729''8364'__70
              (coe
                 d_lookup_158 (coe v0)
                 (coe MAlonzo.Code.Cost.Base.C_BStep_36 (coe v1)))))
      (coe d_ε'8364'_68) (coe MAlonzo.Code.Cost.Base.d_stepKindList_32)
-- Cost._.totalBuiltinCosts
d_totalBuiltinCosts_236 ::
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  T_ExBudget_52 -> T_ExBudget_52
d_totalBuiltinCosts_236 v0 ~v1 = du_totalBuiltinCosts_236 v0
du_totalBuiltinCosts_236 ::
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 -> T_ExBudget_52
du_totalBuiltinCosts_236 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216 (coe d__'8729''8364'__70)
      (coe d_ε'8364'_68)
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe
            (\ v1 ->
               d_lookup_158
                 (coe v0)
                 (coe
                    MAlonzo.Code.Cost.Base.C_BBuiltinApp_40 (coe v1)
                    (coe
                       MAlonzo.Code.Data.Vec.Base.du_replicate_444
                       (coe MAlonzo.Code.Builtin.d_arity_304 (coe v1))
                       (coe
                          MAlonzo.Code.Untyped.CEK.C_V'45'con_50
                          (coe
                             MAlonzo.Code.Builtin.Signature.C_atomic_12
                             (coe MAlonzo.Code.Builtin.Constant.AtomicType.C_aUnit_14))
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))))
         (coe MAlonzo.Code.Builtin.d_builtinList_430))
-- Cost._.getCPU
d_getCPU_244 ::
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  T_ExBudget_52 ->
  T_ExBudget_52 -> MAlonzo.Code.Agda.Builtin.Float.T_Float_6
d_getCPU_244 ~v0 ~v1 v2 = du_getCPU_244 v2
du_getCPU_244 ::
  T_ExBudget_52 -> MAlonzo.Code.Agda.Builtin.Float.T_Float_6
du_getCPU_244 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Float.d_primNatToFloat_24
      (d_ExCPU_58 (coe v0))
-- Cost._.budgetToString
d_budgetToString_248 ::
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  T_ExBudget_52 ->
  T_ExBudget_52 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_budgetToString_248 ~v0 ~v1 v2 = du_budgetToString_248 v2
du_budgetToString_248 ::
  T_ExBudget_52 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
du_budgetToString_248 v0
  = case coe v0 of
      C_mkExBudget_62 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (MAlonzo.Code.Data.String.Base.d_padLeft_60
                (coe ' ') (coe (15 :: Integer))
                (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1))
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("  " :: Data.Text.Text)
                (MAlonzo.Code.Data.String.Base.d_padLeft_60
                   (coe ' ') (coe (15 :: Integer))
                   (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost._.printStepCost
d_printStepCost_254 ::
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  T_ExBudget_52 ->
  MAlonzo.Code.Cost.Base.T_StepKind_6 ->
  T_ExBudget_52 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_printStepCost_254 ~v0 ~v1 v2 v3 = du_printStepCost_254 v2 v3
du_printStepCost_254 ::
  MAlonzo.Code.Cost.Base.T_StepKind_6 ->
  T_ExBudget_52 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
du_printStepCost_254 v0 v1
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (MAlonzo.Code.Data.String.Base.d_padRight_70
         (coe ' ') (coe (10 :: Integer))
         (coe MAlonzo.Code.Cost.Base.d_showStepKind_28 (coe v0)))
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         (" " :: Data.Text.Text)
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            (MAlonzo.Code.Data.String.Base.d_padLeft_60
               (coe ' ') (coe (20 :: Integer))
               (coe du_budgetToString_248 (coe v1)))
            ("\n" :: Data.Text.Text)))
-- Cost._.printStepReport
d_printStepReport_260 ::
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  T_ExBudget_52 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_printStepReport_260 ~v0 ~v1 v2 = du_printStepReport_260 v2
du_printStepReport_260 ::
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_printStepReport_260 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Data.String.Base.d__'43''43'__20
              (coe
                 du_printStepCost_254 (coe v1)
                 (coe
                    d_lookup_158 (coe v0)
                    (coe MAlonzo.Code.Cost.Base.C_BStep_36 (coe v1))))))
      (coe ("" :: Data.Text.Text))
      (coe MAlonzo.Code.Cost.Base.d_stepKindList_32)
-- Cost._.printBuiltinCost
d_printBuiltinCost_268 ::
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  T_ExBudget_52 ->
  MAlonzo.Code.Builtin.T_Builtin_2 ->
  T_ExBudget_52 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_printBuiltinCost_268 ~v0 ~v1 v2 v3
  = du_printBuiltinCost_268 v2 v3
du_printBuiltinCost_268 ::
  MAlonzo.Code.Builtin.T_Builtin_2 ->
  T_ExBudget_52 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
du_printBuiltinCost_268 v0 v1
  = case coe v1 of
      C_mkExBudget_62 v2 v3
        -> let v4
                 = coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                     (MAlonzo.Code.Data.String.Base.d_padRight_70
                        (coe ' ') (coe (22 :: Integer))
                        (coe MAlonzo.Code.Builtin.d_showBuiltin_428 (coe v0)))
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                        (" " :: Data.Text.Text)
                        (coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (coe du_budgetToString_248 (coe v1)) ("\n" :: Data.Text.Text))) in
           coe
             (case coe v2 of
                0 -> case coe v3 of
                       0 -> coe ("" :: Data.Text.Text)
                       _ -> coe v4
                _ -> coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost._.printBuiltinReport
d_printBuiltinReport_276 ::
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  T_ExBudget_52 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_printBuiltinReport_276 ~v0 ~v1 v2 = du_printBuiltinReport_276 v2
du_printBuiltinReport_276 ::
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_printBuiltinReport_276 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Data.String.Base.d__'43''43'__20
              (coe
                 du_printBuiltinCost_268 (coe v1)
                 (coe
                    d_lookup_158 (coe v0)
                    (coe
                       MAlonzo.Code.Cost.Base.C_BBuiltinApp_40 (coe v1)
                       (coe
                          MAlonzo.Code.Data.Vec.Base.du_replicate_444
                          (coe MAlonzo.Code.Builtin.d_arity_304 (coe v1))
                          (coe
                             MAlonzo.Code.Untyped.CEK.C_V'45'con_50
                             (coe
                                MAlonzo.Code.Builtin.Signature.C_atomic_12
                                (coe MAlonzo.Code.Builtin.Constant.AtomicType.C_aUnit_14))
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))))))
      (coe ("" :: Data.Text.Text))
      (coe MAlonzo.Code.Builtin.d_builtinList_430)
-- Cost._.formatTimePicoseconds
d_formatTimePicoseconds_284 ::
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  T_ExBudget_52 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_formatTimePicoseconds_284 ~v0 ~v1 v2
  = du_formatTimePicoseconds_284 v2
du_formatTimePicoseconds_284 ::
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_formatTimePicoseconds_284 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe
         MAlonzo.Code.Agda.Builtin.Float.d_primFloatInequality_8
         (1.0e12 :: Double) v0)
      (coe
         MAlonzo.Code.Text.Printf.d_printf_24 ("%f s" :: Data.Text.Text)
         (coe
            MAlonzo.Code.Agda.Builtin.Float.d_primFloatDiv_54 v0
            (1.0e12 :: Double)))
      (coe
         MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
         (coe
            MAlonzo.Code.Agda.Builtin.Float.d_primFloatInequality_8
            (1.0e9 :: Double) v0)
         (coe
            MAlonzo.Code.Text.Printf.d_printf_24 ("%f ms" :: Data.Text.Text)
            (coe
               MAlonzo.Code.Agda.Builtin.Float.d_primFloatDiv_54 v0
               (1.0e9 :: Double)))
         (coe
            MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
            (coe
               MAlonzo.Code.Agda.Builtin.Float.d_primFloatInequality_8
               (1000000.0 :: Double) v0)
            (coe
               MAlonzo.Code.Text.Printf.d_printf_24 ("%f \956s" :: Data.Text.Text)
               (coe
                  MAlonzo.Code.Agda.Builtin.Float.d_primFloatDiv_54 v0
                  (1000000.0 :: Double)))
            (coe
               MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
               (coe
                  MAlonzo.Code.Agda.Builtin.Float.d_primFloatInequality_8
                  (1000.0 :: Double) v0)
               (coe
                  MAlonzo.Code.Text.Printf.d_printf_24 ("%f ns" :: Data.Text.Text)
                  (coe
                     MAlonzo.Code.Agda.Builtin.Float.d_primFloatDiv_54 v0
                     (1000.0 :: Double)))
               (coe
                  MAlonzo.Code.Text.Printf.d_printf_24 ("%f ps" :: Data.Text.Text)
                  v0))))
