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

module MAlonzo.Code.Data.List.Sort.MergeSort.Properties where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional
import qualified MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.All.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.Linked
import qualified MAlonzo.Code.Data.List.Relation.Unary.Sorted.TotalOrder.Properties
import qualified MAlonzo.Code.Data.List.Sort.Base
import qualified MAlonzo.Code.Data.List.Sort.MergeSort.Base
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Single
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Data.List.Sort.MergeSort.Properties._.SortingAlgorithm
d_SortingAlgorithm_124 a0 a1 a2 a3 = ()
-- Data.List.Sort.MergeSort.Properties._.SortingAlgorithm.sort
d_sort_128 ::
  MAlonzo.Code.Data.List.Sort.Base.T_SortingAlgorithm_236 ->
  [AgdaAny] -> [AgdaAny]
d_sort_128 v0
  = coe MAlonzo.Code.Data.List.Sort.Base.d_sort_248 (coe v0)
-- Data.List.Sort.MergeSort.Properties._.SortingAlgorithm.sort-↗
d_sort'45''8599'_130 ::
  MAlonzo.Code.Data.List.Sort.Base.T_SortingAlgorithm_236 ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28
d_sort'45''8599'_130 v0
  = coe
      MAlonzo.Code.Data.List.Sort.Base.d_sort'45''8599'_256 (coe v0)
-- Data.List.Sort.MergeSort.Properties._.SortingAlgorithm.sort-↭
d_sort'45''8621'_132 ::
  MAlonzo.Code.Data.List.Sort.Base.T_SortingAlgorithm_236 ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
d_sort'45''8621'_132 v0
  = coe
      MAlonzo.Code.Data.List.Sort.Base.d_sort'45''8621'_252 (coe v0)
-- Data.List.Sort.MergeSort.Properties._.mergeAll
d_mergeAll_138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  [[AgdaAny]] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 -> [AgdaAny]
d_mergeAll_138 ~v0 ~v1 ~v2 v3 = du_mergeAll_138 v3
du_mergeAll_138 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  [[AgdaAny]] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 -> [AgdaAny]
du_mergeAll_138 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Sort.MergeSort.Base.du_mergeAll_152 (coe v0)
      v1
-- Data.List.Sort.MergeSort.Properties._.mergePairs
d_mergePairs_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  [[AgdaAny]] -> [[AgdaAny]]
d_mergePairs_140 ~v0 ~v1 ~v2 v3 = du_mergePairs_140 v3
du_mergePairs_140 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  [[AgdaAny]] -> [[AgdaAny]]
du_mergePairs_140 v0
  = coe
      MAlonzo.Code.Data.List.Sort.MergeSort.Base.du_mergePairs_122
      (coe v0)
-- Data.List.Sort.MergeSort.Properties._.sort
d_sort_142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  [AgdaAny] -> [AgdaAny]
d_sort_142 ~v0 ~v1 ~v2 v3 = du_sort_142 v3
du_sort_142 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  [AgdaAny] -> [AgdaAny]
du_sort_142 v0
  = coe
      MAlonzo.Code.Data.List.Sort.MergeSort.Base.du_sort_166 (coe v0)
-- Data.List.Sort.MergeSort.Properties._.Sorted
d_Sorted_146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  [AgdaAny] -> ()
d_Sorted_146 = erased
-- Data.List.Sort.MergeSort.Properties.mergePairs-↭
d_mergePairs'45''8621'_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  [[AgdaAny]] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
d_mergePairs'45''8621'_164 ~v0 ~v1 ~v2 v3 v4
  = du_mergePairs'45''8621'_164 v3 v4
du_mergePairs'45''8621'_164 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  [[AgdaAny]] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
du_mergePairs'45''8621'_164 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'refl_50
      (:) v2 v3
        -> case coe v3 of
             []
               -> coe
                    MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'refl_50
             (:) v4 v5
               -> coe
                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                    (\ v6 v7 v8 ->
                       coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v8)
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          MAlonzo.Code.Data.List.Base.du_merge_192
                          (coe
                             MAlonzo.Code.Relation.Binary.Structures.d__'8804''63'__538
                             (coe
                                MAlonzo.Code.Relation.Binary.Bundles.d_isDecTotalOrder_1098
                                (coe v0)))
                          (coe v2) (coe v4))
                       (coe
                          MAlonzo.Code.Data.List.Base.du_concat_244
                          (coe
                             MAlonzo.Code.Data.List.Sort.MergeSort.Base.du_mergePairs_122
                             (coe v0) (coe v5))))
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2)
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v4)
                          (coe MAlonzo.Code.Data.List.Base.du_concat_244 v5)))
                    (coe
                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621''45''10217'_416
                       (coe
                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                          (\ v6 v7 v8 v9 v10 ->
                             coe
                               MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'trans_84
                               v6 v7 v9 v10))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             MAlonzo.Code.Data.List.Base.du_merge_192
                             (coe
                                MAlonzo.Code.Relation.Binary.Structures.d__'8804''63'__538
                                (coe
                                   MAlonzo.Code.Relation.Binary.Bundles.d_isDecTotalOrder_1098
                                   (coe v0)))
                             (coe v2) (coe v4))
                          (coe
                             MAlonzo.Code.Data.List.Base.du_concat_244
                             (coe
                                MAlonzo.Code.Data.List.Sort.MergeSort.Base.du_mergePairs_122
                                (coe v0) (coe v5))))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2) (coe v4))
                          (coe MAlonzo.Code.Data.List.Base.du_concat_244 v5))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2)
                          (coe
                             MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v4)
                             (coe MAlonzo.Code.Data.List.Base.du_concat_244 v5)))
                       (coe
                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                          (\ v6 v7 v8 v9 v10 -> v10)
                          (coe
                             MAlonzo.Code.Data.List.Base.du__'43''43'__32
                             (coe
                                MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2) (coe v4))
                             (coe MAlonzo.Code.Data.List.Base.du_concat_244 v5))
                          (coe
                             MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2)
                             (coe
                                MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v4)
                                (coe MAlonzo.Code.Data.List.Base.du_concat_244 v5)))
                          (coe
                             MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2)
                             (coe
                                MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v4)
                                (coe MAlonzo.Code.Data.List.Base.du_concat_244 v5)))
                          (let v6
                                 = \ v6 ->
                                     coe
                                       MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'refl_50 in
                           coe
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                   (coe v6))
                                (coe
                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2)
                                   (coe
                                      MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v4)
                                      (coe MAlonzo.Code.Data.List.Base.du_concat_244 v5)))))
                          erased)
                       (coe
                          MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.Properties.du_'43''43''8314'_422
                          (coe
                             MAlonzo.Code.Data.List.Base.du_merge_192
                             (coe
                                MAlonzo.Code.Relation.Binary.Structures.d__'8804''63'__538
                                (coe
                                   MAlonzo.Code.Relation.Binary.Bundles.d_isDecTotalOrder_1098
                                   (coe v0)))
                             (coe v2) (coe v4))
                          (coe
                             MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2) (coe v4))
                          (coe
                             MAlonzo.Code.Data.List.Base.du_concat_244
                             (coe
                                MAlonzo.Code.Data.List.Sort.MergeSort.Base.du_mergePairs_122
                                (coe v0) (coe v5)))
                          (coe
                             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.Properties.du_merge'45''8621'_858
                             (coe
                                MAlonzo.Code.Relation.Binary.Structures.d__'8804''63'__538
                                (coe
                                   MAlonzo.Code.Relation.Binary.Bundles.d_isDecTotalOrder_1098
                                   (coe v0)))
                             (coe v2) (coe v4))
                          (coe du_mergePairs'45''8621'_164 (coe v0) (coe v5))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Sort.MergeSort.Properties.mergeAll-↭
d_mergeAll'45''8621'_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  [[AgdaAny]] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
d_mergeAll'45''8621'_178 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_mergeAll'45''8621'_178 v3 v4
du_mergeAll'45''8621'_178 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  [[AgdaAny]] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
du_mergeAll'45''8621'_178 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'refl_50
      (:) v2 v3
        -> case coe v3 of
             []
               -> coe
                    MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'sym_68
                    (coe MAlonzo.Code.Data.List.Base.du_concat_244 v1)
                    (coe
                       MAlonzo.Code.Data.List.Sort.MergeSort.Base.du_mergeAll_152 (coe v0)
                       (coe v1))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.Properties.du_'43''43''45'identity'691'_724)
             (:) v4 v5
               -> coe
                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                    (\ v6 v7 v8 ->
                       coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v8)
                    (coe
                       MAlonzo.Code.Data.List.Sort.MergeSort.Base.du_mergeAll_152 (coe v0)
                       (coe
                          MAlonzo.Code.Data.List.Sort.MergeSort.Base.du_mergePairs_122
                          (coe v0) (coe v1)))
                    (coe MAlonzo.Code.Data.List.Base.du_concat_244 v1)
                    (coe
                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621''45''10217'_416
                       (coe
                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                          (\ v6 v7 v8 v9 v10 ->
                             coe
                               MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'trans_84
                               v6 v7 v9 v10))
                       (coe
                          MAlonzo.Code.Data.List.Sort.MergeSort.Base.du_mergeAll_152 (coe v0)
                          (coe
                             MAlonzo.Code.Data.List.Sort.MergeSort.Base.du_mergePairs_122
                             (coe v0) (coe v1)))
                       (coe
                          MAlonzo.Code.Data.List.Base.du_concat_244
                          (coe
                             MAlonzo.Code.Data.List.Sort.MergeSort.Base.du_mergePairs_122
                             (coe v0) (coe v1)))
                       (coe MAlonzo.Code.Data.List.Base.du_concat_244 v1)
                       (coe
                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621''45''10217'_416
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                             (\ v6 v7 v8 v9 v10 ->
                                coe
                                  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'trans_84
                                  v6 v7 v9 v10))
                          (coe
                             MAlonzo.Code.Data.List.Base.du_concat_244
                             (coe
                                MAlonzo.Code.Data.List.Sort.MergeSort.Base.du_mergePairs_122
                                (coe v0) (coe v1)))
                          (coe MAlonzo.Code.Data.List.Base.du_concat_244 v1)
                          (coe MAlonzo.Code.Data.List.Base.du_concat_244 v1)
                          (let v6
                                 = \ v6 ->
                                     coe
                                       MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'refl_50 in
                           coe
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                   (coe v6))
                                (coe MAlonzo.Code.Data.List.Base.du_concat_244 v1)))
                          (coe du_mergePairs'45''8621'_164 (coe v0) (coe v1)))
                       (coe
                          du_mergeAll'45''8621'_178 (coe v0)
                          (coe
                             MAlonzo.Code.Data.List.Sort.MergeSort.Base.du_mergePairs_122
                             (coe v0) (coe v1))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Sort.MergeSort.Properties.sort-↭
d_sort'45''8621'_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
d_sort'45''8621'_192 ~v0 ~v1 ~v2 v3 v4
  = du_sort'45''8621'_192 v3 v4
du_sort'45''8621'_192 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
du_sort'45''8621'_192 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v4)
      (coe
         MAlonzo.Code.Data.List.Sort.MergeSort.Base.du_mergeAll_152 (coe v0)
         (coe
            MAlonzo.Code.Data.List.Base.du_map_22
            (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270) (coe v1)))
      v1
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621''45''10217'_416
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (\ v2 v3 v4 v5 v6 ->
               coe
                 MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'trans_84
                 v2 v3 v5 v6))
         (coe
            MAlonzo.Code.Data.List.Sort.MergeSort.Base.du_mergeAll_152 (coe v0)
            (coe
               MAlonzo.Code.Data.List.Base.du_map_22
               (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270) (coe v1)))
         (coe
            MAlonzo.Code.Data.List.Base.du_concat_244
            (coe
               MAlonzo.Code.Data.List.Base.du_map_22
               (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270) (coe v1)))
         v1
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
            (\ v2 v3 v4 v5 v6 -> v6)
            (coe
               MAlonzo.Code.Data.List.Base.du_concat_244
               (coe
                  MAlonzo.Code.Data.List.Base.du_map_22
                  (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270) (coe v1)))
            v1 v1
            (let v2
                   = \ v2 ->
                       coe
                         MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'refl_50 in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                     (coe v2))
                  (coe v1)))
            erased)
         (coe
            du_mergeAll'45''8621'_178 (coe v0)
            (coe
               MAlonzo.Code.Data.List.Base.du_map_22
               (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270) (coe v1))))
-- Data.List.Sort.MergeSort.Properties.mergePairs-↗
d_mergePairs'45''8599'_198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  [[AgdaAny]] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_mergePairs'45''8599'_198 ~v0 ~v1 ~v2 v3 v4 v5
  = du_mergePairs'45''8599'_198 v3 v4 v5
du_mergePairs'45''8599'_198 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  [[AgdaAny]] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_mergePairs'45''8599'_198 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50 -> coe v2
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v5 v6
        -> case coe v1 of
             (:) v7 v8
               -> case coe v6 of
                    MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v5 v6
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v11 v12
                      -> case coe v8 of
                           (:) v13 v14
                             -> coe
                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                  (coe
                                     MAlonzo.Code.Data.List.Relation.Unary.Sorted.TotalOrder.Properties.du_merge'8314'_768
                                     (coe v0) (coe v7) (coe v13) (coe v5) (coe v11))
                                  (coe du_mergePairs'45''8599'_198 (coe v0) (coe v14) (coe v12))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Sort.MergeSort.Properties.mergeAll-↗
d_mergeAll'45''8599'_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  [[AgdaAny]] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28
d_mergeAll'45''8599'_212 ~v0 ~v1 ~v2 v3 v4 ~v5 v6
  = du_mergeAll'45''8599'_212 v3 v4 v6
du_mergeAll'45''8599'_212 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  [[AgdaAny]] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28
du_mergeAll'45''8599'_212 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
        -> coe MAlonzo.Code.Data.List.Relation.Unary.Linked.C_'91''93'_32
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v5 v6
        -> case coe v6 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50 -> coe v5
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v9 v10
               -> coe
                    du_mergeAll'45''8599'_212 (coe v0)
                    (coe
                       MAlonzo.Code.Data.List.Sort.MergeSort.Base.du_mergePairs_122
                       (coe v0) (coe v1))
                    (coe
                       du_mergePairs'45''8599'_198 (coe v0) (coe v1)
                       (coe
                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v5
                          (coe
                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v9 v10)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Sort.MergeSort.Properties.sort-↗
d_sort'45''8599'_230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28
d_sort'45''8599'_230 ~v0 ~v1 ~v2 v3 v4
  = du_sort'45''8599'_230 v3 v4
du_sort'45''8599'_230 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28
du_sort'45''8599'_230 v0 v1
  = coe
      du_mergeAll'45''8599'_212 (coe v0)
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe
            (\ v2 ->
               coe
                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
         (coe v1))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_map'8314'_496
         (coe v1)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.du_universal_520
            (coe
               (\ v2 ->
                  coe
                    MAlonzo.Code.Data.List.Relation.Unary.Linked.C_'91''45''93'_36))
            (coe v1)))
-- Data.List.Sort.MergeSort.Properties.mergeSort
d_mergeSort_236 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  MAlonzo.Code.Data.List.Sort.Base.T_SortingAlgorithm_236
d_mergeSort_236 ~v0 ~v1 ~v2 v3 = du_mergeSort_236 v3
du_mergeSort_236 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076 ->
  MAlonzo.Code.Data.List.Sort.Base.T_SortingAlgorithm_236
du_mergeSort_236 v0
  = coe
      MAlonzo.Code.Data.List.Sort.Base.C_SortingAlgorithm'46'constructor_2133
      (coe
         MAlonzo.Code.Data.List.Sort.MergeSort.Base.du_sort_166 (coe v0))
      (coe du_sort'45''8621'_192 (coe v0))
      (coe du_sort'45''8599'_230 (coe v0))
