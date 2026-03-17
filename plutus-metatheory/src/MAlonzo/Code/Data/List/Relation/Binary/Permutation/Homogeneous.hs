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

module MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Fin.Permutation
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties
import qualified MAlonzo.Code.Function.Bundles
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Data.List.Relation.Binary.Permutation.Homogeneous.Permutation
d_Permutation_32 a0 a1 a2 a3 a4 a5 = ()
data T_Permutation_32
  = C_refl_42 MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 |
    C_prep_54 AgdaAny T_Permutation_32 |
    C_swap_72 AgdaAny AgdaAny T_Permutation_32 |
    C_trans_80 [AgdaAny] T_Permutation_32 T_Permutation_32
-- Data.List.Relation.Binary.Permutation.Homogeneous.sym
d_sym_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] -> [AgdaAny] -> T_Permutation_32 -> T_Permutation_32
d_sym_82 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_sym_82 v4 v5 v6 v7
du_sym_82 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] -> [AgdaAny] -> T_Permutation_32 -> T_Permutation_32
du_sym_82 v0 v1 v2 v3
  = case coe v3 of
      C_refl_42 v6
        -> coe
             C_refl_42
             (coe
                MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_symmetric_40
                (coe v0) (coe v1) (coe v2) (coe v6))
      C_prep_54 v8 v9
        -> case coe v1 of
             (:) v10 v11
               -> case coe v2 of
                    (:) v12 v13
                      -> coe
                           C_prep_54 (coe v0 v10 v12 v8)
                           (coe du_sym_82 (coe v0) (coe v11) (coe v13) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_swap_72 v10 v11 v12
        -> case coe v1 of
             (:) v13 v14
               -> case coe v14 of
                    (:) v15 v16
                      -> case coe v2 of
                           (:) v17 v18
                             -> case coe v18 of
                                  (:) v19 v20
                                    -> coe
                                         C_swap_72 (coe v0 v15 v17 v11) (coe v0 v13 v19 v10)
                                         (coe du_sym_82 (coe v0) (coe v16) (coe v20) (coe v12))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_trans_80 v5 v7 v8
        -> coe
             C_trans_80 v5 (coe du_sym_82 (coe v0) (coe v5) (coe v2) (coe v8))
             (coe du_sym_82 (coe v0) (coe v1) (coe v5) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Homogeneous.isEquivalence
d_isEquivalence_108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_108 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_isEquivalence_108 v4 v5
du_isEquivalence_108 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_108 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsEquivalence'46'constructor_745
      (coe
         (\ v2 ->
            coe
              C_refl_42
              (coe
                 MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_refl_30
                 (coe v0) (coe v2))))
      (coe du_sym_82 (coe v1))
      (\ v2 v3 v4 v5 v6 -> coe C_trans_80 v3 v5 v6)
-- Data.List.Relation.Binary.Permutation.Homogeneous.setoid
d_setoid_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_114 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_setoid_114 v4 v5
du_setoid_114 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_114 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Setoid'46'constructor_761
      (coe du_isEquivalence_108 (coe v0) (coe v1))
-- Data.List.Relation.Binary.Permutation.Homogeneous.map
d_map_122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] -> [AgdaAny] -> T_Permutation_32 -> T_Permutation_32
d_map_122 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
  = du_map_122 v6 v7 v8 v9
du_map_122 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] -> [AgdaAny] -> T_Permutation_32 -> T_Permutation_32
du_map_122 v0 v1 v2 v3
  = case coe v3 of
      C_refl_42 v6
        -> coe
             C_refl_42
             (coe
                MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.du_map_120
                (coe v0) (coe v1) (coe v2) (coe v6))
      C_prep_54 v8 v9
        -> case coe v1 of
             (:) v10 v11
               -> case coe v2 of
                    (:) v12 v13
                      -> coe
                           C_prep_54 (coe v0 v10 v12 v8)
                           (coe du_map_122 (coe v0) (coe v11) (coe v13) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_swap_72 v10 v11 v12
        -> case coe v1 of
             (:) v13 v14
               -> case coe v14 of
                    (:) v15 v16
                      -> case coe v2 of
                           (:) v17 v18
                             -> case coe v18 of
                                  (:) v19 v20
                                    -> coe
                                         C_swap_72 (coe v0 v13 v19 v10) (coe v0 v15 v17 v11)
                                         (coe du_map_122 (coe v0) (coe v16) (coe v20) (coe v12))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_trans_80 v5 v7 v8
        -> coe
             C_trans_80 v5 (coe du_map_122 (coe v0) (coe v1) (coe v5) (coe v7))
             (coe du_map_122 (coe v0) (coe v5) (coe v2) (coe v8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Homogeneous.steps
d_steps_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  [AgdaAny] -> [AgdaAny] -> T_Permutation_32 -> Integer
d_steps_152 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_steps_152 v4 v5 v6
du_steps_152 ::
  [AgdaAny] -> [AgdaAny] -> T_Permutation_32 -> Integer
du_steps_152 v0 v1 v2
  = case coe v2 of
      C_refl_42 v5 -> coe (1 :: Integer)
      C_prep_54 v7 v8
        -> case coe v0 of
             (:) v9 v10
               -> case coe v1 of
                    (:) v11 v12
                      -> coe
                           addInt (coe (1 :: Integer))
                           (coe du_steps_152 (coe v10) (coe v12) (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_swap_72 v9 v10 v11
        -> case coe v0 of
             (:) v12 v13
               -> case coe v13 of
                    (:) v14 v15
                      -> case coe v1 of
                           (:) v16 v17
                             -> case coe v17 of
                                  (:) v18 v19
                                    -> coe
                                         addInt (coe (1 :: Integer))
                                         (coe du_steps_152 (coe v15) (coe v19) (coe v11))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_trans_80 v4 v6 v7
        -> coe
             addInt (coe du_steps_152 (coe v0) (coe v4) (coe v6))
             (coe du_steps_152 (coe v4) (coe v1) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Homogeneous.onIndices
d_onIndices_166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  [AgdaAny] ->
  [AgdaAny] ->
  T_Permutation_32 -> MAlonzo.Code.Function.Bundles.T_Inverse_2068
d_onIndices_166 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_onIndices_166 v4 v5 v6
du_onIndices_166 ::
  [AgdaAny] ->
  [AgdaAny] ->
  T_Permutation_32 -> MAlonzo.Code.Function.Bundles.T_Inverse_2068
du_onIndices_166 v0 v1 v2
  = case coe v2 of
      C_refl_42 v5
        -> coe
             MAlonzo.Code.Data.Fin.Permutation.du_cast'45'id_66
             (coe
                MAlonzo.Code.Data.List.Base.du_foldr_216
                (let v6 = \ v6 -> addInt (coe (1 :: Integer)) (coe v6) in
                 coe (coe (\ v7 -> v6)))
                (coe (0 :: Integer)) (coe v0))
             (coe
                MAlonzo.Code.Data.List.Base.du_foldr_216
                (let v6 = \ v6 -> addInt (coe (1 :: Integer)) (coe v6) in
                 coe (coe (\ v7 -> v6)))
                (coe (0 :: Integer)) (coe v1))
      C_prep_54 v7 v8
        -> case coe v0 of
             (:) v9 v10
               -> case coe v1 of
                    (:) v11 v12
                      -> coe
                           MAlonzo.Code.Data.Fin.Permutation.du_lift'8320'_140
                           (coe du_onIndices_166 (coe v10) (coe v12) (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_swap_72 v9 v10 v11
        -> case coe v0 of
             (:) v12 v13
               -> case coe v13 of
                    (:) v14 v15
                      -> case coe v1 of
                           (:) v16 v17
                             -> case coe v17 of
                                  (:) v18 v19
                                    -> coe
                                         MAlonzo.Code.Data.Fin.Permutation.du_swap_288
                                         (coe du_onIndices_166 (coe v15) (coe v19) (coe v11))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_trans_80 v4 v6 v7
        -> coe
             MAlonzo.Code.Data.Fin.Permutation.du__'8728''8346'__60
             (coe du_onIndices_166 (coe v0) (coe v4) (coe v6))
             (coe du_onIndices_166 (coe v4) (coe v1) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
