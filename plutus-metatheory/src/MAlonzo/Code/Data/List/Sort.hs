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

module MAlonzo.Code.Data.List.Sort where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous
import qualified MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional
import qualified MAlonzo.Code.Data.List.Relation.Unary.Linked
import qualified MAlonzo.Code.Data.List.Sort.Base
import qualified MAlonzo.Code.Data.List.Sort.MergeSort.Properties
import qualified MAlonzo.Code.Relation.Binary.Bundles

-- Data.List.Sort._.SortingAlgorithm
d_SortingAlgorithm_120 a0 a1 a2 a3 = ()
-- Data.List.Sort._.SortingAlgorithm.sort
d_sort_124 ::
  MAlonzo.Code.Data.List.Sort.Base.T_SortingAlgorithm_236 ->
  [AgdaAny] -> [AgdaAny]
d_sort_124 v0
  = coe MAlonzo.Code.Data.List.Sort.Base.d_sort_248 (coe v0)
-- Data.List.Sort._.SortingAlgorithm.sort-↗
d_sort'45''8599'_126 ::
  MAlonzo.Code.Data.List.Sort.Base.T_SortingAlgorithm_236 ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28
d_sort'45''8599'_126 v0
  = coe
      MAlonzo.Code.Data.List.Sort.Base.d_sort'45''8599'_256 (coe v0)
-- Data.List.Sort._.SortingAlgorithm.sort-↭
d_sort'45''8621'_128 ::
  MAlonzo.Code.Data.List.Sort.Base.T_SortingAlgorithm_236 ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
d_sort'45''8621'_128 v0
  = coe
      MAlonzo.Code.Data.List.Sort.Base.d_sort'45''8621'_252 (coe v0)
-- Data.List.Sort._.SortingAlgorithm.sort-↭ₛ
d_sort'45''8621''8347'_130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  MAlonzo.Code.Data.List.Sort.Base.T_SortingAlgorithm_236 ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_sort'45''8621''8347'_130 ~v0 ~v1 ~v2 v3
  = du_sort'45''8621''8347'_130 v3
du_sort'45''8621''8347'_130 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  MAlonzo.Code.Data.List.Sort.Base.T_SortingAlgorithm_236 ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_sort'45''8621''8347'_130 v0
  = coe
      MAlonzo.Code.Data.List.Sort.Base.du_sort'45''8621''8347'_260
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_1160 (coe v0))
-- Data.List.Sort.sortingAlgorithm
d_sortingAlgorithm_136 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  MAlonzo.Code.Data.List.Sort.Base.T_SortingAlgorithm_236
d_sortingAlgorithm_136 ~v0 ~v1 ~v2 v3 = du_sortingAlgorithm_136 v3
du_sortingAlgorithm_136 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  MAlonzo.Code.Data.List.Sort.Base.T_SortingAlgorithm_236
du_sortingAlgorithm_136 v0
  = coe
      MAlonzo.Code.Data.List.Sort.MergeSort.Properties.du_mergeSort_236
      (coe v0)
-- Data.List.Sort._.sort
d_sort_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  [AgdaAny] -> [AgdaAny]
d_sort_140 ~v0 ~v1 ~v2 v3 = du_sort_140 v3
du_sort_140 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  [AgdaAny] -> [AgdaAny]
du_sort_140 v0
  = coe
      MAlonzo.Code.Data.List.Sort.Base.d_sort_248
      (coe du_sortingAlgorithm_136 (coe v0))
-- Data.List.Sort._.sort-↗
d_sort'45''8599'_142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28
d_sort'45''8599'_142 ~v0 ~v1 ~v2 v3 = du_sort'45''8599'_142 v3
du_sort'45''8599'_142 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28
du_sort'45''8599'_142 v0
  = coe
      MAlonzo.Code.Data.List.Sort.Base.d_sort'45''8599'_256
      (coe du_sortingAlgorithm_136 (coe v0))
-- Data.List.Sort._.sort-↭
d_sort'45''8621'_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
d_sort'45''8621'_144 ~v0 ~v1 ~v2 v3 = du_sort'45''8621'_144 v3
du_sort'45''8621'_144 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
du_sort'45''8621'_144 v0
  = coe
      MAlonzo.Code.Data.List.Sort.Base.d_sort'45''8621'_252
      (coe du_sortingAlgorithm_136 (coe v0))
