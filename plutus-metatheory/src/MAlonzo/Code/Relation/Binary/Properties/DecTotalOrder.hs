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

module MAlonzo.Code.Relation.Binary.Properties.DecTotalOrder where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd
import qualified MAlonzo.Code.Relation.Binary.Construct.NonStrictToStrict
import qualified MAlonzo.Code.Relation.Binary.Definitions
import qualified MAlonzo.Code.Relation.Binary.Properties.Poset
import qualified MAlonzo.Code.Relation.Binary.Properties.Preorder
import qualified MAlonzo.Code.Relation.Binary.Properties.TotalOrder
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Relation.Binary.Properties.DecTotalOrder._._∼ᵒ_
d__'8764''7506'__30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  AgdaAny -> AgdaAny -> ()
d__'8764''7506'__30 = erased
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties._<_
d__'60'__120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  AgdaAny -> AgdaAny -> ()
d__'60'__120 = erased
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.asym
d_asym_122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_asym_122 = erased
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.irrefl
d_irrefl_124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irrefl_124 = erased
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.<-isStrictPartialOrder
d_'60''45'isStrictPartialOrder_126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370
d_'60''45'isStrictPartialOrder_126 ~v0 ~v1 ~v2 v3
  = du_'60''45'isStrictPartialOrder_126 v3
du_'60''45'isStrictPartialOrder_126 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370
du_'60''45'isStrictPartialOrder_126 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_1182 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Properties.Poset.du_'60''45'isStrictPartialOrder_178
         (coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_1018 (coe v1)))
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.<-resp-≈
d_'60''45'resp'45''8776'_128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'45''8776'_128 ~v0 ~v1 ~v2 v3
  = du_'60''45'resp'45''8776'_128 v3
du_'60''45'resp'45''8776'_128 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''45'resp'45''8776'_128 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_1182 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Relation.Binary.Bundles.du_poset_1018 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_'60''45'resp'45''8776'_388
            (coe
               MAlonzo.Code.Relation.Binary.Properties.Poset.du_'60''45'isStrictPartialOrder_178
               (coe v2))))
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.<-respʳ-≈
d_'60''45'resp'691''45''8776'_130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'691''45''8776'_130 ~v0 ~v1 ~v2 v3
  = du_'60''45'resp'691''45''8776'_130 v3
du_'60''45'resp'691''45''8776'_130 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''45'resp'691''45''8776'_130 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_1182 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Relation.Binary.Bundles.du_poset_1018 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Relation.Binary.Properties.Poset.du_'60''45'strictPartialOrder_180
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'60''45'resp'691''45''8776'_408
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_782
                  (coe v3)))))
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.<-respˡ-≈
d_'60''45'resp'737''45''8776'_132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'737''45''8776'_132 ~v0 ~v1 ~v2 v3
  = du_'60''45'resp'737''45''8776'_132 v3
du_'60''45'resp'737''45''8776'_132 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''45'resp'737''45''8776'_132 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_1182 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Relation.Binary.Bundles.du_poset_1018 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Relation.Binary.Properties.Poset.du_'60''45'strictPartialOrder_180
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'60''45'resp'737''45''8776'_410
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_782
                  (coe v3)))))
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.<-strictPartialOrder
d_'60''45'strictPartialOrder_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_760
d_'60''45'strictPartialOrder_134 ~v0 ~v1 ~v2 v3
  = du_'60''45'strictPartialOrder_134 v3
du_'60''45'strictPartialOrder_134 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_760
du_'60''45'strictPartialOrder_134 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_1182 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Properties.Poset.du_'60''45'strictPartialOrder_180
         (coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_1018 (coe v1)))
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.trans
d_trans_136 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_trans_136 ~v0 ~v1 ~v2 v3 = du_trans_136 v3
du_trans_136 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_trans_136 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_1182 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Relation.Binary.Bundles.du_poset_1018 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_386
            (coe
               MAlonzo.Code.Relation.Binary.Properties.Poset.du_'60''45'isStrictPartialOrder_178
               (coe v2))))
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.<⇒≉
d_'60''8658''8777'_138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''8658''8777'_138 = erased
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.<⇒≱
d_'60''8658''8817'_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''8658''8817'_140 = erased
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.≤⇒≯
d_'8804''8658''8815'_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8804''8658''8815'_144 = erased
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.≤∧≉⇒<
d_'8804''8743''8777''8658''60'_146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8804''8743''8777''8658''60'_146 ~v0 ~v1 ~v2 ~v3
  = du_'8804''8743''8777''8658''60'_146
du_'8804''8743''8777''8658''60'_146 ::
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8804''8743''8777''8658''60'_146 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Properties.Poset.du_'8804''8743''8777''8658''60'_208
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.antisym
d_antisym_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_148 ~v0 ~v1 ~v2 v3 = du_antisym_148 v3
du_antisym_148 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_antisym_148 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_1182 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Relation.Binary.Bundles.du_poset_1018 (coe v1) in
       coe
         (coe
            (\ v3 v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
                 (MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_514
                    (coe v2))
                 v3 v4 v6 v5)))
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.≥-isPartialOrder
d_'8805''45'isPartialOrder_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_'8805''45'isPartialOrder_150 ~v0 ~v1 ~v2 v3
  = du_'8805''45'isPartialOrder_150 v3
du_'8805''45'isPartialOrder_150 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
du_'8805''45'isPartialOrder_150 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_1182 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Properties.Poset.du_'8805''45'isPartialOrder_150
         (coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_1018 (coe v1)))
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.converse-isPreorder
d_converse'45'isPreorder_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_converse'45'isPreorder_152 ~v0 ~v1 ~v2 v3
  = du_converse'45'isPreorder_152 v3
du_converse'45'isPreorder_152 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
du_converse'45'isPreorder_152 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_1182 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Relation.Binary.Bundles.du_poset_1018 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Properties.Preorder.du_converse'45'isPreorder_86
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.du_preorder_522 (coe v2))))
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.≥-isTotalOrder
d_'8805''45'isTotalOrder_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_488
d_'8805''45'isTotalOrder_154 ~v0 ~v1 ~v2 v3
  = du_'8805''45'isTotalOrder_154 v3
du_'8805''45'isTotalOrder_154 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_488
du_'8805''45'isTotalOrder_154 v0
  = coe
      MAlonzo.Code.Relation.Binary.Properties.TotalOrder.du_'8805''45'isTotalOrder_210
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_1182 (coe v0))
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.≥-poset
d_'8805''45'poset_156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
d_'8805''45'poset_156 ~v0 ~v1 ~v2 v3 = du_'8805''45'poset_156 v3
du_'8805''45'poset_156 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
du_'8805''45'poset_156 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_1182 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Properties.Poset.du_'8805''45'poset_152
         (coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_1018 (coe v1)))
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.converse-preorder
d_converse'45'preorder_158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
d_converse'45'preorder_158 ~v0 ~v1 ~v2 v3
  = du_converse'45'preorder_158 v3
du_converse'45'preorder_158 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
du_converse'45'preorder_158 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_1182 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Relation.Binary.Bundles.du_poset_1018 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Properties.Preorder.du_converse'45'preorder_88
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.du_preorder_522 (coe v2))))
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.refl
d_refl_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  AgdaAny -> AgdaAny
d_refl_160 ~v0 ~v1 ~v2 v3 = du_refl_160 v3
du_refl_160 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  AgdaAny -> AgdaAny
du_refl_160 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_1182 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Relation.Binary.Bundles.du_poset_1018 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Relation.Binary.Properties.Poset.du_'8805''45'poset_152
                    (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Relation.Binary.Bundles.du_preorder_522 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_refl_104
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_164 (coe v4))))))
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.reflexive
d_reflexive_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_162 ~v0 ~v1 ~v2 v3 = du_reflexive_162 v3
du_reflexive_162 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_reflexive_162 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_1182 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Relation.Binary.Bundles.du_poset_1018 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Relation.Binary.Properties.Poset.du_'8805''45'poset_152
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_514
                     (coe v3))))))
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.total
d_total_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_total_164 ~v0 ~v1 ~v2 v3 = du_total_164 v3
du_total_164 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_total_164 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_1182 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_total_498
         (coe
            MAlonzo.Code.Relation.Binary.Properties.TotalOrder.du_'8805''45'isTotalOrder_210
            (coe v1)))
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.≥-totalOrder
d_'8805''45'totalOrder_166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986
d_'8805''45'totalOrder_166 ~v0 ~v1 ~v2 v3
  = du_'8805''45'totalOrder_166 v3
du_'8805''45'totalOrder_166 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986
du_'8805''45'totalOrder_166 v0
  = coe
      MAlonzo.Code.Relation.Binary.Properties.TotalOrder.du_'8805''45'totalOrder_212
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_1182 (coe v0))
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.trans
d_trans_168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_168 ~v0 ~v1 ~v2 v3 = du_trans_168 v3
du_trans_168 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_168 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_1182 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Relation.Binary.Bundles.du_poset_1018 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Relation.Binary.Properties.Poset.du_'8805''45'poset_152
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_90
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_514
                     (coe v3))))))
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.≰-respʳ-≈
d_'8816''45'resp'691''45''8776'_170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8816''45'resp'691''45''8776'_170 = erased
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.≰-respˡ-≈
d_'8816''45'resp'737''45''8776'_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8816''45'resp'737''45''8776'_172 = erased
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.≰⇒>
d_'8816''8658''62'_174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8816''8658''62'_174 ~v0 ~v1 ~v2 v3 = du_'8816''8658''62'_174 v3
du_'8816''8658''62'_174 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8816''8658''62'_174 v0
  = coe
      MAlonzo.Code.Relation.Binary.Properties.TotalOrder.du_'8816''8658''62'_222
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_1182 (coe v0))
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.≰⇒≥
d_'8816''8658''8805'_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny
d_'8816''8658''8805'_176 ~v0 ~v1 ~v2 v3
  = du_'8816''8658''8805'_176 v3
du_'8816''8658''8805'_176 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny
du_'8816''8658''8805'_176 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Properties.TotalOrder.du_'8816''8658''8805'_228
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_1182 (coe v0))
      v1 v2
-- Relation.Binary.Properties.DecTotalOrder.≥-isDecTotalOrder
d_'8805''45'isDecTotalOrder_224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_546
d_'8805''45'isDecTotalOrder_224 ~v0 ~v1 ~v2 v3
  = du_'8805''45'isDecTotalOrder_224 v3
du_'8805''45'isDecTotalOrder_224 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_546
du_'8805''45'isDecTotalOrder_224 v0
  = coe
      MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_isDecTotalOrder_450
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isDecTotalOrder_1120
         (coe v0))
-- Relation.Binary.Properties.DecTotalOrder.≥-decTotalOrder
d_'8805''45'decTotalOrder_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098
d_'8805''45'decTotalOrder_226 ~v0 ~v1 ~v2 v3
  = du_'8805''45'decTotalOrder_226 v3
du_'8805''45'decTotalOrder_226 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098
du_'8805''45'decTotalOrder_226 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_1272
      (coe du_'8805''45'isDecTotalOrder_224 (coe v0))
-- Relation.Binary.Properties.DecTotalOrder._._≤?_
d__'8804''63'__230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8804''63'__230 ~v0 ~v1 ~v2 v3 = du__'8804''63'__230 v3
du__'8804''63'__230 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8804''63'__230 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d__'8804''63'__560
      (coe du_'8805''45'isDecTotalOrder_224 (coe v0))
-- Relation.Binary.Properties.DecTotalOrder.<-isStrictTotalOrder
d_'60''45'isStrictTotalOrder_232 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624
d_'60''45'isStrictTotalOrder_232 ~v0 ~v1 ~v2 v3
  = du_'60''45'isStrictTotalOrder_232 v3
du_'60''45'isStrictTotalOrder_232 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624
du_'60''45'isStrictTotalOrder_232 v0
  = coe
      MAlonzo.Code.Relation.Binary.Construct.NonStrictToStrict.du_'60''45'isStrictTotalOrder'8322'_604
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isDecTotalOrder_1120
         (coe v0))
-- Relation.Binary.Properties.DecTotalOrder.<-strictTotalOrder
d_'60''45'strictTotalOrder_234 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280
d_'60''45'strictTotalOrder_234 ~v0 ~v1 ~v2 v3
  = du_'60''45'strictTotalOrder_234 v3
du_'60''45'strictTotalOrder_234 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280
du_'60''45'strictTotalOrder_234 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_1386
      (coe du_'60''45'isStrictTotalOrder_232 (coe v0))
-- Relation.Binary.Properties.DecTotalOrder._._≁_
d__'8769'__238 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  AgdaAny -> AgdaAny -> ()
d__'8769'__238 = erased
-- Relation.Binary.Properties.DecTotalOrder._.compare
d_compare_240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
d_compare_240 ~v0 ~v1 ~v2 v3 = du_compare_240 v3
du_compare_240 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
du_compare_240 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_compare_634
      (coe du_'60''45'isStrictTotalOrder_232 (coe v0))
-- Relation.Binary.Properties.DecTotalOrder.≮⇒≥
d_'8814''8658''8805'_246 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny
d_'8814''8658''8805'_246 ~v0 ~v1 ~v2 v3 v4 v5
  = du_'8814''8658''8805'_246 v3 v4 v5
du_'8814''8658''8805'_246 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny
du_'8814''8658''8805'_246 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Construct.NonStrictToStrict.du_'8814''8658''8805'_126
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_38
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_496
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isTotalOrder_556
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isDecTotalOrder_1120
                        (coe v0)))))))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d__'8799'__558
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isDecTotalOrder_1120
            (coe v0)))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_496
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isTotalOrder_556
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isDecTotalOrder_1120
                     (coe v0))))))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_total_498
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isTotalOrder_556
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isDecTotalOrder_1120
               (coe v0))))
      (coe v1) (coe v2)
