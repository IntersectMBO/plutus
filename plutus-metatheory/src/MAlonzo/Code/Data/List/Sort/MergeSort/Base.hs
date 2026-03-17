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

module MAlonzo.Code.Data.List.Sort.MergeSort.Base where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Data.List.Sort.MergeSort.Base.mergePairs
d_mergePairs_122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  [[AgdaAny]] -> [[AgdaAny]]
d_mergePairs_122 ~v0 ~v1 ~v2 v3 v4 = du_mergePairs_122 v3 v4
du_mergePairs_122 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  [[AgdaAny]] -> [[AgdaAny]]
du_mergePairs_122 v0 v1
  = case coe v1 of
      (:) v2 v3
        -> case coe v3 of
             (:) v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Data.List.Base.du_merge_192
                       (coe
                          MAlonzo.Code.Relation.Binary.Structures.d__'8804''63'__538
                          (coe
                             MAlonzo.Code.Relation.Binary.Bundles.d_isDecTotalOrder_1098
                             (coe v0)))
                       (coe v2) (coe v4))
                    (coe du_mergePairs_122 (coe v0) (coe v5))
             _ -> coe v1
      _ -> coe v1
-- Data.List.Sort.MergeSort.Base.length-mergePairs
d_length'45'mergePairs_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [[AgdaAny]] -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_length'45'mergePairs_140 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_length'45'mergePairs_140 v6
du_length'45'mergePairs_140 ::
  [[AgdaAny]] -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_length'45'mergePairs_140 v0
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (coe
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
      (:) v1 v2
        -> case coe v2 of
             []
               -> coe
                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (coe
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                          (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)))
             (:) v3 v4
               -> coe
                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_m'60'n'8658'm'60'1'43'n_3118
                       (coe du_length'45'mergePairs_140 (coe v4)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Sort.MergeSort.Base.mergeAll
d_mergeAll_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  [[AgdaAny]] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 -> [AgdaAny]
d_mergeAll_152 ~v0 ~v1 ~v2 v3 v4 ~v5 = du_mergeAll_152 v3 v4
du_mergeAll_152 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  [[AgdaAny]] -> [AgdaAny]
du_mergeAll_152 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> case coe v3 of
             [] -> coe v2
             (:) v4 v5
               -> coe
                    du_mergeAll_152 (coe v0) (coe du_mergePairs_122 (coe v0) (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Sort.MergeSort.Base.sort
d_sort_166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  [AgdaAny] -> [AgdaAny]
d_sort_166 ~v0 ~v1 ~v2 v3 v4 = du_sort_166 v3 v4
du_sort_166 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  [AgdaAny] -> [AgdaAny]
du_sort_166 v0 v1
  = coe
      du_mergeAll_152 (coe v0)
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270) (coe v1))
