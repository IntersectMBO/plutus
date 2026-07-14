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
import qualified MAlonzo.Code.Cost.Size
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

-- Cost.AVL._∈?_
d__'8712''63'__4 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 -> Bool
d__'8712''63'__4 v0 v1
  = coe
      MAlonzo.Code.Data.Tree.AVL.Map.du__'8712''63'__268
      (coe
         MAlonzo.Code.Data.String.Properties.d_'60''45'strictTotalOrder'45''8776'_76)
-- Cost.AVL.Map
d_Map_6 :: MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()
d_Map_6 = erased
-- Cost.AVL.delete
d_delete_8 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266
d_delete_8 v0 v1
  = coe
      MAlonzo.Code.Data.Tree.AVL.Map.du_delete_218
      (coe
         MAlonzo.Code.Data.String.Properties.d_'60''45'strictTotalOrder'45''8776'_76)
-- Cost.AVL.empty
d_empty_10 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Data.Tree.AVL.T_Tree_266
d_empty_10 v0 v1 = coe MAlonzo.Code.Data.Tree.AVL.Map.du_empty_210
-- Cost.AVL.foldr
d_foldr_12 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Data.Tree.AVL.T_Tree_266 -> AgdaAny
d_foldr_12 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Data.Tree.AVL.Map.du_foldr_232 v4
-- Cost.AVL.fromList
d_fromList_14 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266
d_fromList_14 v0 v1
  = coe
      MAlonzo.Code.Data.Tree.AVL.Map.du_fromList_238
      (coe
         MAlonzo.Code.Data.String.Properties.d_'60''45'strictTotalOrder'45''8776'_76)
-- Cost.AVL.headTail
d_headTail_16 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_headTail_16 v0 v1
  = coe
      MAlonzo.Code.Data.Tree.AVL.Map.du_headTail_228
      (coe
         MAlonzo.Code.Data.String.Properties.d_'60''45'strictTotalOrder'45''8776'_76)
-- Cost.AVL.initLast
d_initLast_18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_initLast_18 v0 v1
  = coe
      MAlonzo.Code.Data.Tree.AVL.Map.du_initLast_230
      (coe
         MAlonzo.Code.Data.String.Properties.d_'60''45'strictTotalOrder'45''8776'_76)
-- Cost.AVL.insert
d_insert_20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266
d_insert_20 v0 v1
  = coe
      MAlonzo.Code.Data.Tree.AVL.Map.du_insert_214
      (coe
         MAlonzo.Code.Data.String.Properties.d_'60''45'strictTotalOrder'45''8776'_76)
-- Cost.AVL.insertWith
d_insertWith_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  (Maybe AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266
d_insertWith_22 v0 v1
  = coe
      MAlonzo.Code.Data.Tree.AVL.Map.du_insertWith_216
      (coe
         MAlonzo.Code.Data.String.Properties.d_'60''45'strictTotalOrder'45''8776'_76)
-- Cost.AVL.intersection
d_intersection_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266
d_intersection_24 v0 v1
  = coe
      MAlonzo.Code.Data.Tree.AVL.Map.du_intersection_260
      (coe
         MAlonzo.Code.Data.String.Properties.d_'60''45'strictTotalOrder'45''8776'_76)
-- Cost.AVL.intersectionWith
d_intersectionWith_26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266
d_intersectionWith_26 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Data.Tree.AVL.Map.du_intersectionWith_256
      (coe
         MAlonzo.Code.Data.String.Properties.d_'60''45'strictTotalOrder'45''8776'_76)
      v6
-- Cost.AVL.intersections
d_intersections_28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [MAlonzo.Code.Data.Tree.AVL.T_Tree_266] ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266
d_intersections_28 v0 v1
  = coe
      MAlonzo.Code.Data.Tree.AVL.Map.du_intersections_266
      (coe
         MAlonzo.Code.Data.String.Properties.d_'60''45'strictTotalOrder'45''8776'_76)
-- Cost.AVL.intersectionsWith
d_intersectionsWith_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Data.Tree.AVL.T_Tree_266] ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266
d_intersectionsWith_30 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Tree.AVL.Map.du_intersectionsWith_262
      (coe
         MAlonzo.Code.Data.String.Properties.d_'60''45'strictTotalOrder'45''8776'_76)
      v2
-- Cost.AVL.lookup
d_lookup_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny
d_lookup_32 v0 v1
  = coe
      MAlonzo.Code.Data.Tree.AVL.Map.du_lookup_220
      (coe
         MAlonzo.Code.Data.String.Properties.d_'60''45'strictTotalOrder'45''8776'_76)
-- Cost.AVL.map
d_map_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266
d_map_34 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Data.Tree.AVL.Map.du_map_222 v4
-- Cost.AVL.member
d_member_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 -> Bool
d_member_36 v0 v1
  = coe
      MAlonzo.Code.Data.Tree.AVL.Map.du_member_226
      (coe
         MAlonzo.Code.Data.String.Properties.d_'60''45'strictTotalOrder'45''8776'_76)
-- Cost.AVL.singleton
d_singleton_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny -> MAlonzo.Code.Data.Tree.AVL.T_Tree_266
d_singleton_38 v0 v1
  = coe MAlonzo.Code.Data.Tree.AVL.Map.du_singleton_212
-- Cost.AVL.size
d_size_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Data.Tree.AVL.T_Tree_266 -> Integer
d_size_40 v0 v1 = coe MAlonzo.Code.Data.Tree.AVL.Map.du_size_242
-- Cost.AVL.toList
d_toList_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_toList_42 v0 v1
  = coe MAlonzo.Code.Data.Tree.AVL.Map.du_toList_240
-- Cost.AVL.union
d_union_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266
d_union_44 v0 v1
  = coe
      MAlonzo.Code.Data.Tree.AVL.Map.du_union_248
      (coe
         MAlonzo.Code.Data.String.Properties.d_'60''45'strictTotalOrder'45''8776'_76)
-- Cost.AVL.unionWith
d_unionWith_46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Maybe AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266
d_unionWith_46 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.Tree.AVL.Map.du_unionWith_244
      (coe
         MAlonzo.Code.Data.String.Properties.d_'60''45'strictTotalOrder'45''8776'_76)
      v4
-- Cost.AVL.unions
d_unions_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [MAlonzo.Code.Data.Tree.AVL.T_Tree_266] ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266
d_unions_48 v0 v1
  = coe
      MAlonzo.Code.Data.Tree.AVL.Map.du_unions_254
      (coe
         MAlonzo.Code.Data.String.Properties.d_'60''45'strictTotalOrder'45''8776'_76)
-- Cost.AVL.unionsWith
d_unionsWith_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Maybe AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Data.Tree.AVL.T_Tree_266] ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266
d_unionsWith_50 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Tree.AVL.Map.du_unionsWith_250
      (coe
         MAlonzo.Code.Data.String.Properties.d_'60''45'strictTotalOrder'45''8776'_76)
      v2
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
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoidExBudget_80
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_758
      (coe
         MAlonzo.Code.Algebra.Structures.C_constructor_522
         (coe
            MAlonzo.Code.Algebra.Structures.C_constructor_210
            (coe
               MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
            erased)
         erased)
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
-- Cost.measures
d_measures_96 ::
  MAlonzo.Code.Builtin.T_Builtin_2 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_measures_96 v0
  = let v1
          = coe
              MAlonzo.Code.Data.Vec.Base.du_replicate_444
              (coe MAlonzo.Code.Builtin.d_arity_318 (coe v0))
              (coe MAlonzo.Code.Cost.Size.d_defaultValueMeasure_86) in
    coe
      (case coe v0 of
         MAlonzo.Code.Builtin.C_insertCoin_112
           -> coe
                MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                MAlonzo.Code.Cost.Size.d_defaultValueMeasure_86
                (coe
                   MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                   MAlonzo.Code.Cost.Size.d_defaultValueMeasure_86
                   (coe
                      MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                      MAlonzo.Code.Cost.Size.d_defaultValueMeasure_86
                      (coe
                         MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                         MAlonzo.Code.Cost.Size.d_valueMaxDepthMeasure_92
                         (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32))))
         MAlonzo.Code.Builtin.C_lookupCoin_114
           -> coe
                MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                MAlonzo.Code.Cost.Size.d_defaultValueMeasure_86
                (coe
                   MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                   MAlonzo.Code.Cost.Size.d_defaultValueMeasure_86
                   (coe
                      MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                      MAlonzo.Code.Cost.Size.d_valueMaxDepthMeasure_92
                      (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)))
         MAlonzo.Code.Builtin.C_unValueData_124
           -> coe
                MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                MAlonzo.Code.Cost.Size.d_dataNodeCountMeasure_96
                (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)
         MAlonzo.Code.Builtin.C_integerToByteString_172
           -> coe
                MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                MAlonzo.Code.Cost.Size.d_defaultValueMeasure_86
                (coe
                   MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                   MAlonzo.Code.Cost.Size.d_numBytesAsWords_100
                   (coe
                      MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                      MAlonzo.Code.Cost.Size.d_defaultValueMeasure_86
                      (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)))
         _ -> coe v1)
-- Cost.builtinCost
d_builtinCost_100 ::
  MAlonzo.Code.Builtin.T_Builtin_2 ->
  MAlonzo.Code.Cost.Model.T_BuiltinModel_68 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> T_ExBudget_52
d_builtinCost_100 v0 v1 v2
  = coe
      C_mkExBudget_62
      (coe
         MAlonzo.Code.Cost.Model.d_runModel_104
         (coe MAlonzo.Code.Builtin.d_arity_318 (coe v0))
         (coe MAlonzo.Code.Cost.Model.d_costingCPU_76 (coe v1))
         (coe du_sizes_112 (coe v0) (coe v2)))
      (coe
         MAlonzo.Code.Cost.Model.d_runModel_104
         (coe MAlonzo.Code.Builtin.d_arity_318 (coe v0))
         (coe MAlonzo.Code.Cost.Model.d_costingMem_78 (coe v1))
         (coe du_sizes_112 (coe v0) (coe v2)))
-- Cost._.sizes
d_sizes_112 ::
  MAlonzo.Code.Builtin.T_Builtin_2 ->
  MAlonzo.Code.Cost.Model.T_BuiltinModel_68 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_sizes_112 v0 ~v1 v2 = du_sizes_112 v0 v2
du_sizes_112 ::
  MAlonzo.Code.Builtin.T_Builtin_2 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
du_sizes_112 v0 v1
  = coe
      MAlonzo.Code.Data.Vec.Base.du_zipWith_242 (coe (\ v2 -> v2))
      (coe d_measures_96 (coe v0)) (coe v1)
-- Cost.CostModel
d_CostModel_114 :: ()
d_CostModel_114 = erased
-- Cost.cekMachineCostFunction
d_cekMachineCostFunction_116 ::
  MAlonzo.Code.Cost.Raw.T_HCekMachineCosts_4 ->
  MAlonzo.Code.Cost.Base.T_StepKind_6 -> T_ExBudget_52
d_cekMachineCostFunction_116 v0 v1
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
d_exBudgetCategoryCost_136 ::
  MAlonzo.Code.Utils.T__'215'__436
    MAlonzo.Code.Cost.Raw.T_HCekMachineCosts_4
    (MAlonzo.Code.Builtin.T_Builtin_2 ->
     MAlonzo.Code.Cost.Model.T_BuiltinModel_68) ->
  MAlonzo.Code.Cost.Base.T_ExBudgetCategory_34 -> T_ExBudget_52
d_exBudgetCategoryCost_136 v0 v1
  = case coe v0 of
      MAlonzo.Code.Utils.C__'44'__450 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Cost.Base.C_BStep_36 v4
               -> coe d_cekMachineCostFunction_116 (coe v2) (coe v4)
             MAlonzo.Code.Cost.Base.C_BBuiltinApp_40 v4 v5
               -> coe d_builtinCost_100 (coe v4) (coe v3 v4) (coe v5)
             MAlonzo.Code.Cost.Base.C_BStartup_42
               -> coe
                    d_fromHExBudget_64
                    (coe MAlonzo.Code.Cost.Raw.d_getCekStartupCost_8 v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.machineParameters
d_machineParameters_150 ::
  MAlonzo.Code.Utils.T__'215'__436
    MAlonzo.Code.Cost.Raw.T_HCekMachineCosts_4
    (MAlonzo.Code.Builtin.T_Builtin_2 ->
     MAlonzo.Code.Cost.Model.T_BuiltinModel_68) ->
  MAlonzo.Code.Cost.Base.T_MachineParameters_46
d_machineParameters_150 v0
  = coe
      MAlonzo.Code.Cost.Base.C_constructor_68
      (coe d_exBudgetCategoryCost_136 (coe v0)) (coe d_ε'8364'_68)
      (coe d__'8729''8364'__70) (coe d_isMonoidExBudget_80)
-- Cost.countingReport
d_countingReport_154 ::
  T_ExBudget_52 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_countingReport_154 v0
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
d_mkKeyFromExBudgetCategory_160 ::
  MAlonzo.Code.Cost.Base.T_ExBudgetCategory_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_mkKeyFromExBudgetCategory_160 v0
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
             (MAlonzo.Code.Builtin.d_showBuiltin_492 (coe v1))
      MAlonzo.Code.Cost.Base.C_BStartup_42 -> coe ("2" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.TallyingBudget
d_TallyingBudget_166 :: ()
d_TallyingBudget_166 = erased
-- Cost.lookup
d_lookup_168 ::
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Cost.Base.T_ExBudgetCategory_34 -> T_ExBudget_52
d_lookup_168 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Data.Tree.AVL.du_lookup_324
              (coe
                 MAlonzo.Code.Data.String.Properties.d_'60''45'strictTotalOrder'45''8776'_76)
              (coe MAlonzo.Code.Data.Tree.AVL.Value.du_const_96) (coe v0)
              (coe d_mkKeyFromExBudgetCategory_160 (coe v1)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3 -> coe v3
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe d_ε'8364'_68
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Cost.εT
d_εT_188 ::
  MAlonzo.Code.Utils.T__'215'__436
    MAlonzo.Code.Data.Tree.AVL.T_Tree_266 T_ExBudget_52
d_εT_188
  = coe
      MAlonzo.Code.Utils.C__'44'__450
      (coe MAlonzo.Code.Data.Tree.AVL.Map.du_empty_210)
      (coe d_ε'8364'_68)
-- Cost._∙T_
d__'8729'T__190 ::
  MAlonzo.Code.Utils.T__'215'__436
    MAlonzo.Code.Data.Tree.AVL.T_Tree_266 T_ExBudget_52 ->
  MAlonzo.Code.Utils.T__'215'__436
    MAlonzo.Code.Data.Tree.AVL.T_Tree_266 T_ExBudget_52 ->
  MAlonzo.Code.Utils.T__'215'__436
    MAlonzo.Code.Data.Tree.AVL.T_Tree_266 T_ExBudget_52
d__'8729'T__190 v0 v1
  = case coe v0 of
      MAlonzo.Code.Utils.C__'44'__450 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Utils.C__'44'__450 v4 v5
               -> coe
                    MAlonzo.Code.Utils.C__'44'__450
                    (coe
                       MAlonzo.Code.Data.Tree.AVL.Map.du_unionWith_244
                       MAlonzo.Code.Data.String.Properties.d_'60''45'strictTotalOrder'45''8776'_76
                       (coe du_u_204) v2 v4)
                    (coe d__'8729''8364'__70 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost._.u
d_u_204 ::
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  T_ExBudget_52 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  T_ExBudget_52 ->
  T_ExBudget_52 -> Maybe T_ExBudget_52 -> T_ExBudget_52
d_u_204 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_u_204 v4 v5
du_u_204 :: T_ExBudget_52 -> Maybe T_ExBudget_52 -> T_ExBudget_52
du_u_204 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe d__'8729''8364'__70 (coe v0) (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.TallyingBudget-assoc
d_TallyingBudget'45'assoc_212
  = error
      "MAlonzo Runtime Error: postulate evaluated: Cost.TallyingBudget-assoc"
-- Cost.Tallying-budget-identityʳ
d_Tallying'45'budget'45'identity'691'_214
  = error
      "MAlonzo Runtime Error: postulate evaluated: Cost.Tallying-budget-identity\691"
-- Cost.isMonoidTallyingBudget
d_isMonoidTallyingBudget_216 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoidTallyingBudget_216
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_758
      (coe
         MAlonzo.Code.Algebra.Structures.C_constructor_522
         (coe
            MAlonzo.Code.Algebra.Structures.C_constructor_210
            (coe
               MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
            erased)
         erased)
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
-- Cost.tallyingCekMachineCost
d_tallyingCekMachineCost_222 ::
  MAlonzo.Code.Utils.T__'215'__436
    MAlonzo.Code.Cost.Raw.T_HCekMachineCosts_4
    (MAlonzo.Code.Builtin.T_Builtin_2 ->
     MAlonzo.Code.Cost.Model.T_BuiltinModel_68) ->
  MAlonzo.Code.Cost.Base.T_ExBudgetCategory_34 ->
  MAlonzo.Code.Utils.T__'215'__436
    MAlonzo.Code.Data.Tree.AVL.T_Tree_266 T_ExBudget_52
d_tallyingCekMachineCost_222 v0 v1
  = coe
      MAlonzo.Code.Utils.C__'44'__450
      (coe
         MAlonzo.Code.Data.Tree.AVL.Map.du_singleton_212
         (d_mkKeyFromExBudgetCategory_160 (coe v1))
         (d_exBudgetCategoryCost_136 (coe v0) (coe v1)))
      (coe d_exBudgetCategoryCost_136 (coe v0) (coe v1))
-- Cost.tallyingMachineParameters
d_tallyingMachineParameters_230 ::
  MAlonzo.Code.Utils.T__'215'__436
    MAlonzo.Code.Cost.Raw.T_HCekMachineCosts_4
    (MAlonzo.Code.Builtin.T_Builtin_2 ->
     MAlonzo.Code.Cost.Model.T_BuiltinModel_68) ->
  MAlonzo.Code.Cost.Base.T_MachineParameters_46
d_tallyingMachineParameters_230 v0
  = coe
      MAlonzo.Code.Cost.Base.C_constructor_68
      (coe d_tallyingCekMachineCost_222 (coe v0)) (coe d_εT_188)
      (coe d__'8729'T__190) (coe d_isMonoidTallyingBudget_216)
-- Cost.tallyingReport
d_tallyingReport_234 ::
  MAlonzo.Code.Utils.T__'215'__436
    MAlonzo.Code.Data.Tree.AVL.T_Tree_266 T_ExBudget_52 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_tallyingReport_234 v0
  = case coe v0 of
      MAlonzo.Code.Utils.C__'44'__450 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (d_countingReport_154 (coe v2))
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("\n" :: Data.Text.Text)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("\n" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (coe du_printStepReport_270 (coe v1))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("\n" :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            ("startup    " :: Data.Text.Text)
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               (coe
                                  du_budgetToString_258
                                  (coe
                                     d_lookup_168 (coe v1)
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
                                           du_budgetToString_258
                                           (coe du_totalComputeCost_244 (coe v1)))
                                        (coe
                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                           ("\n" :: Data.Text.Text)
                                           (coe
                                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                              ("\n\n" :: Data.Text.Text)
                                              (coe
                                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                 (coe du_printBuiltinReport_286 (coe v1))
                                                 (coe
                                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                    ("\n" :: Data.Text.Text)
                                                    (coe
                                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                       ("Total builtin costs:   " :: Data.Text.Text)
                                                       (coe
                                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                          (coe
                                                             du_budgetToString_258
                                                             (coe
                                                                du_totalBuiltinCosts_246 (coe v1)))
                                                          (coe
                                                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                             ("\n" :: Data.Text.Text)
                                                             (coe
                                                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                (coe
                                                                   MAlonzo.Code.Text.Printf.d_printf_26
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
                                                                            du_getCPU_254
                                                                            (coe
                                                                               du_totalBuiltinCosts_246
                                                                               (coe v1))))
                                                                      (coe du_getCPU_254 (coe v2))))
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
                                                                               du_budgetToString_258
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
                                                                                     du_formatTimePicoseconds_294
                                                                                     (coe
                                                                                        du_getCPU_254
                                                                                        (coe
                                                                                           v2))))))))))))))))))))))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost._.totalComputeCost
d_totalComputeCost_244 ::
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  T_ExBudget_52 -> T_ExBudget_52
d_totalComputeCost_244 v0 ~v1 = du_totalComputeCost_244 v0
du_totalComputeCost_244 ::
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 -> T_ExBudget_52
du_totalComputeCost_244 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216
      (coe
         (\ v1 ->
            d__'8729''8364'__70
              (coe
                 d_lookup_168 (coe v0)
                 (coe MAlonzo.Code.Cost.Base.C_BStep_36 (coe v1)))))
      (coe d_ε'8364'_68) (coe MAlonzo.Code.Cost.Base.d_stepKindList_32)
-- Cost._.totalBuiltinCosts
d_totalBuiltinCosts_246 ::
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  T_ExBudget_52 -> T_ExBudget_52
d_totalBuiltinCosts_246 v0 ~v1 = du_totalBuiltinCosts_246 v0
du_totalBuiltinCosts_246 ::
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 -> T_ExBudget_52
du_totalBuiltinCosts_246 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216 (coe d__'8729''8364'__70)
      (coe d_ε'8364'_68)
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe
            (\ v1 ->
               d_lookup_168
                 (coe v0)
                 (coe
                    MAlonzo.Code.Cost.Base.C_BBuiltinApp_40 (coe v1)
                    (coe
                       MAlonzo.Code.Data.Vec.Base.du_replicate_444
                       (coe MAlonzo.Code.Builtin.d_arity_318 (coe v1))
                       (coe
                          MAlonzo.Code.Untyped.CEK.C_V'45'con_50
                          (coe
                             MAlonzo.Code.Builtin.Signature.C_atomic_12
                             (coe MAlonzo.Code.Builtin.Constant.AtomicType.C_aUnit_14))
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))))
         (coe MAlonzo.Code.Builtin.d_builtinList_494))
-- Cost._.getCPU
d_getCPU_254 ::
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  T_ExBudget_52 ->
  T_ExBudget_52 -> MAlonzo.Code.Agda.Builtin.Float.T_Float_6
d_getCPU_254 ~v0 ~v1 v2 = du_getCPU_254 v2
du_getCPU_254 ::
  T_ExBudget_52 -> MAlonzo.Code.Agda.Builtin.Float.T_Float_6
du_getCPU_254 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Float.d_primNatToFloat_24
      (d_ExCPU_58 (coe v0))
-- Cost._.budgetToString
d_budgetToString_258 ::
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  T_ExBudget_52 ->
  T_ExBudget_52 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_budgetToString_258 ~v0 ~v1 v2 = du_budgetToString_258 v2
du_budgetToString_258 ::
  T_ExBudget_52 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
du_budgetToString_258 v0
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
d_printStepCost_264 ::
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  T_ExBudget_52 ->
  MAlonzo.Code.Cost.Base.T_StepKind_6 ->
  T_ExBudget_52 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_printStepCost_264 ~v0 ~v1 v2 v3 = du_printStepCost_264 v2 v3
du_printStepCost_264 ::
  MAlonzo.Code.Cost.Base.T_StepKind_6 ->
  T_ExBudget_52 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
du_printStepCost_264 v0 v1
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
               (coe du_budgetToString_258 (coe v1)))
            ("\n" :: Data.Text.Text)))
-- Cost._.printStepReport
d_printStepReport_270 ::
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  T_ExBudget_52 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_printStepReport_270 ~v0 ~v1 v2 = du_printStepReport_270 v2
du_printStepReport_270 ::
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_printStepReport_270 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Data.String.Base.d__'43''43'__20
              (coe
                 du_printStepCost_264 (coe v1)
                 (coe
                    d_lookup_168 (coe v0)
                    (coe MAlonzo.Code.Cost.Base.C_BStep_36 (coe v1))))))
      (coe ("" :: Data.Text.Text))
      (coe MAlonzo.Code.Cost.Base.d_stepKindList_32)
-- Cost._.printBuiltinCost
d_printBuiltinCost_278 ::
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  T_ExBudget_52 ->
  MAlonzo.Code.Builtin.T_Builtin_2 ->
  T_ExBudget_52 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_printBuiltinCost_278 ~v0 ~v1 v2 v3
  = du_printBuiltinCost_278 v2 v3
du_printBuiltinCost_278 ::
  MAlonzo.Code.Builtin.T_Builtin_2 ->
  T_ExBudget_52 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
du_printBuiltinCost_278 v0 v1
  = case coe v1 of
      C_mkExBudget_62 v2 v3
        -> let v4
                 = coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                     (MAlonzo.Code.Data.String.Base.d_padRight_70
                        (coe ' ') (coe (22 :: Integer))
                        (coe MAlonzo.Code.Builtin.d_showBuiltin_492 (coe v0)))
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                        (" " :: Data.Text.Text)
                        (coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (coe du_budgetToString_258 (coe v1)) ("\n" :: Data.Text.Text))) in
           coe
             (case coe v2 of
                0 -> case coe v3 of
                       0 -> coe ("" :: Data.Text.Text)
                       _ -> coe v4
                _ -> coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost._.printBuiltinReport
d_printBuiltinReport_286 ::
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  T_ExBudget_52 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_printBuiltinReport_286 ~v0 ~v1 v2 = du_printBuiltinReport_286 v2
du_printBuiltinReport_286 ::
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_printBuiltinReport_286 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Data.String.Base.d__'43''43'__20
              (coe
                 du_printBuiltinCost_278 (coe v1)
                 (coe
                    d_lookup_168 (coe v0)
                    (coe
                       MAlonzo.Code.Cost.Base.C_BBuiltinApp_40 (coe v1)
                       (coe
                          MAlonzo.Code.Data.Vec.Base.du_replicate_444
                          (coe MAlonzo.Code.Builtin.d_arity_318 (coe v1))
                          (coe
                             MAlonzo.Code.Untyped.CEK.C_V'45'con_50
                             (coe
                                MAlonzo.Code.Builtin.Signature.C_atomic_12
                                (coe MAlonzo.Code.Builtin.Constant.AtomicType.C_aUnit_14))
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))))))
      (coe ("" :: Data.Text.Text))
      (coe MAlonzo.Code.Builtin.d_builtinList_494)
-- Cost._.formatTimePicoseconds
d_formatTimePicoseconds_294 ::
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  T_ExBudget_52 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_formatTimePicoseconds_294 ~v0 ~v1 v2
  = du_formatTimePicoseconds_294 v2
du_formatTimePicoseconds_294 ::
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_formatTimePicoseconds_294 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe
         MAlonzo.Code.Agda.Builtin.Float.d_primFloatInequality_8
         (1.0e12 :: Double) v0)
      (coe
         MAlonzo.Code.Text.Printf.d_printf_26 ("%f s" :: Data.Text.Text)
         (coe
            MAlonzo.Code.Agda.Builtin.Float.d_primFloatDiv_54 v0
            (1.0e12 :: Double)))
      (coe
         MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
         (coe
            MAlonzo.Code.Agda.Builtin.Float.d_primFloatInequality_8
            (1.0e9 :: Double) v0)
         (coe
            MAlonzo.Code.Text.Printf.d_printf_26 ("%f ms" :: Data.Text.Text)
            (coe
               MAlonzo.Code.Agda.Builtin.Float.d_primFloatDiv_54 v0
               (1.0e9 :: Double)))
         (coe
            MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
            (coe
               MAlonzo.Code.Agda.Builtin.Float.d_primFloatInequality_8
               (1000000.0 :: Double) v0)
            (coe
               MAlonzo.Code.Text.Printf.d_printf_26 ("%f \956s" :: Data.Text.Text)
               (coe
                  MAlonzo.Code.Agda.Builtin.Float.d_primFloatDiv_54 v0
                  (1000000.0 :: Double)))
            (coe
               MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
               (coe
                  MAlonzo.Code.Agda.Builtin.Float.d_primFloatInequality_8
                  (1000.0 :: Double) v0)
               (coe
                  MAlonzo.Code.Text.Printf.d_printf_26 ("%f ns" :: Data.Text.Text)
                  (coe
                     MAlonzo.Code.Agda.Builtin.Float.d_primFloatDiv_54 v0
                     (1000.0 :: Double)))
               (coe
                  MAlonzo.Code.Text.Printf.d_printf_26 ("%f ps" :: Data.Text.Text)
                  v0))))
