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

module MAlonzo.Code.Data.List.Relation.Unary.Sorted.TotalOrder where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.List.Relation.Unary.Linked
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Data.List.Relation.Unary.Sorted.TotalOrder.Sorted
d_Sorted_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_966 ->
  [AgdaAny] -> ()
d_Sorted_106 = erased
-- Data.List.Relation.Unary.Sorted.TotalOrder._.head
d_head_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_966 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28 -> AgdaAny
d_head_120 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_head_120
du_head_120 ::
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28 -> AgdaAny
du_head_120
  = coe MAlonzo.Code.Data.List.Relation.Unary.Linked.du_head_60
-- Data.List.Relation.Unary.Sorted.TotalOrder._.tail
d_tail_122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_966 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28 ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28
d_tail_122 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_tail_122
du_tail_122 ::
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28 ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28
du_tail_122
  = coe MAlonzo.Code.Data.List.Relation.Unary.Linked.du_tail_70
-- Data.List.Relation.Unary.Sorted.TotalOrder.sorted?
d_sorted'63'_124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_966 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_sorted'63'_124 ~v0 ~v1 ~v2 ~v3 = du_sorted'63'_124
du_sorted'63'_124 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_sorted'63'_124
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.Linked.du_linked'63'_218
-- Data.List.Relation.Unary.Sorted.TotalOrder.irrelevant
d_irrelevant_126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_966 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28 ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_irrelevant_126 = erased
-- Data.List.Relation.Unary.Sorted.TotalOrder.satisfiable
d_satisfiable_128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_966 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_satisfiable_128 ~v0 ~v1 ~v2 ~v3 = du_satisfiable_128
du_satisfiable_128 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_satisfiable_128
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.Linked.du_satisfiable_250
