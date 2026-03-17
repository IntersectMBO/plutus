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

module MAlonzo.Code.Data.List.Sort.MergeSort where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.List.Sort.Base
import qualified MAlonzo.Code.Data.List.Sort.MergeSort.Base
import qualified MAlonzo.Code.Data.List.Sort.MergeSort.Properties
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Relation.Binary.Bundles

-- Data.List.Sort.MergeSort._.mergeAll
d_mergeAll_18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  [[AgdaAny]] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 -> [AgdaAny]
d_mergeAll_18 ~v0 ~v1 ~v2 v3 = du_mergeAll_18 v3
du_mergeAll_18 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  [[AgdaAny]] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 -> [AgdaAny]
du_mergeAll_18 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Sort.MergeSort.Base.du_mergeAll_152 (coe v0)
      v1
-- Data.List.Sort.MergeSort._.mergePairs
d_mergePairs_20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  [[AgdaAny]] -> [[AgdaAny]]
d_mergePairs_20 ~v0 ~v1 ~v2 v3 = du_mergePairs_20 v3
du_mergePairs_20 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  [[AgdaAny]] -> [[AgdaAny]]
du_mergePairs_20 v0
  = coe
      MAlonzo.Code.Data.List.Sort.MergeSort.Base.du_mergePairs_122
      (coe v0)
-- Data.List.Sort.MergeSort._.sort
d_sort_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  [AgdaAny] -> [AgdaAny]
d_sort_22 ~v0 ~v1 ~v2 v3 = du_sort_22 v3
du_sort_22 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  [AgdaAny] -> [AgdaAny]
du_sort_22 v0
  = coe
      MAlonzo.Code.Data.List.Sort.MergeSort.Base.du_sort_166 (coe v0)
-- Data.List.Sort.MergeSort._.mergeSort
d_mergeSort_26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  MAlonzo.Code.Data.List.Sort.Base.T_SortingAlgorithm_236
d_mergeSort_26 ~v0 ~v1 ~v2 v3 = du_mergeSort_26 v3
du_mergeSort_26 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  MAlonzo.Code.Data.List.Sort.Base.T_SortingAlgorithm_236
du_mergeSort_26 v0
  = coe
      MAlonzo.Code.Data.List.Sort.MergeSort.Properties.du_mergeSort_236
      (coe v0)
