{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE EmptyCase                 #-}
{-# LANGUAGE EmptyDataDecls            #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE PatternSynonyms           #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module MAlonzo.Code.Relation.Binary.Properties.TotalOrder where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.Irrelevant qualified
import MAlonzo.Code.Data.Sum.Base qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Consequences qualified
import MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd qualified
import MAlonzo.Code.Relation.Binary.Construct.NonStrictToStrict qualified
import MAlonzo.Code.Relation.Binary.Properties.Poset qualified
import MAlonzo.Code.Relation.Binary.Properties.Preorder qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.Code.Relation.Nullary.Decidable.Core qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Relation.Binary.Properties.TotalOrder._._≳_
d__'8819'__24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> ()
d__'8819'__24 = erased
-- Relation.Binary.Properties.TotalOrder._._⋦_
d__'8934'__26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> ()
d__'8934'__26 = erased
-- Relation.Binary.Properties.TotalOrder.PosetProperties._<_
d__'60'__142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> ()
d__'60'__142 = erased
-- Relation.Binary.Properties.TotalOrder.PosetProperties.asym
d_asym_146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_asym_146 = erased
-- Relation.Binary.Properties.TotalOrder.PosetProperties.irrefl
d_irrefl_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irrefl_148 = erased
-- Relation.Binary.Properties.TotalOrder.PosetProperties.<-isStrictPartialOrder
d_'60''45'isStrictPartialOrder_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
d_'60''45'isStrictPartialOrder_150 ~v0 ~v1 ~v2 v3
  = du_'60''45'isStrictPartialOrder_150 v3
du_'60''45'isStrictPartialOrder_150 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
du_'60''45'isStrictPartialOrder_150 v0
  = coe
      MAlonzo.Code.Relation.Binary.Properties.Poset.du_'60''45'isStrictPartialOrder_170
      (coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v0))
-- Relation.Binary.Properties.TotalOrder.PosetProperties.<-resp-≈
d_'60''45'resp'45''8776'_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'45''8776'_152 ~v0 ~v1 ~v2 v3
  = du_'60''45'resp'45''8776'_152 v3
du_'60''45'resp'45''8776'_152 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''45'resp'45''8776'_152 v0
  = let v1
          = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_'60''45'resp'45''8776'_308
         (coe
            MAlonzo.Code.Relation.Binary.Properties.Poset.du_'60''45'isStrictPartialOrder_170
            (coe v1)))
-- Relation.Binary.Properties.TotalOrder.PosetProperties.<-respʳ-≈
d_'60''45'resp'691''45''8776'_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'691''45''8776'_154 ~v0 ~v1 ~v2 v3
  = du_'60''45'resp'691''45''8776'_154 v3
du_'60''45'resp'691''45''8776'_154 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''45'resp'691''45''8776'_154 v0
  = let v1
          = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Relation.Binary.Properties.Poset.du_'60''45'strictPartialOrder_172
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'60''45'resp'691''45''8776'_328
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_578
               (coe v2))))
-- Relation.Binary.Properties.TotalOrder.PosetProperties.<-respˡ-≈
d_'60''45'resp'737''45''8776'_156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'737''45''8776'_156 ~v0 ~v1 ~v2 v3
  = du_'60''45'resp'737''45''8776'_156 v3
du_'60''45'resp'737''45''8776'_156 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''45'resp'737''45''8776'_156 v0
  = let v1
          = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Relation.Binary.Properties.Poset.du_'60''45'strictPartialOrder_172
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'60''45'resp'737''45''8776'_330
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_578
               (coe v2))))
-- Relation.Binary.Properties.TotalOrder.PosetProperties.<-strictPartialOrder
d_'60''45'strictPartialOrder_158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556
d_'60''45'strictPartialOrder_158 ~v0 ~v1 ~v2 v3
  = du_'60''45'strictPartialOrder_158 v3
du_'60''45'strictPartialOrder_158 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556
du_'60''45'strictPartialOrder_158 v0
  = coe
      MAlonzo.Code.Relation.Binary.Properties.Poset.du_'60''45'strictPartialOrder_172
      (coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v0))
-- Relation.Binary.Properties.TotalOrder.PosetProperties.trans
d_trans_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_trans_160 ~v0 ~v1 ~v2 v3 = du_trans_160 v3
du_trans_160 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_trans_160 v0
  = let v1
          = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_306
         (coe
            MAlonzo.Code.Relation.Binary.Properties.Poset.du_'60''45'isStrictPartialOrder_170
            (coe v1)))
-- Relation.Binary.Properties.TotalOrder.PosetProperties.<⇒≉
d_'60''8658''8777'_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''8658''8777'_162 = erased
-- Relation.Binary.Properties.TotalOrder.PosetProperties.<⇒≱
d_'60''8658''8817'_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''8658''8817'_164 = erased
-- Relation.Binary.Properties.TotalOrder.PosetProperties.≤⇒≯
d_'8804''8658''8815'_174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8804''8658''8815'_174 = erased
-- Relation.Binary.Properties.TotalOrder.PosetProperties.≤∧≉⇒<
d_'8804''8743''8777''8658''60'_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8804''8743''8777''8658''60'_176 ~v0 ~v1 ~v2 ~v3
  = du_'8804''8743''8777''8658''60'_176
du_'8804''8743''8777''8658''60'_176 ::
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8804''8743''8777''8658''60'_176 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Properties.Poset.du_'8804''8743''8777''8658''60'_200
-- Relation.Binary.Properties.TotalOrder.PosetProperties.antisym
d_antisym_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_178 ~v0 ~v1 ~v2 v3 = du_antisym_178 v3
du_antisym_178 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_antisym_178 v0
  = let v1
          = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v0) in
    coe
      (coe
         (\ v2 v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
              (MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_336
                 (coe v1))
              v2 v3 v5 v4))
-- Relation.Binary.Properties.TotalOrder.PosetProperties.≥-isPartialOrder
d_'8805''45'isPartialOrder_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_'8805''45'isPartialOrder_180 ~v0 ~v1 ~v2 v3
  = du_'8805''45'isPartialOrder_180 v3
du_'8805''45'isPartialOrder_180 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
du_'8805''45'isPartialOrder_180 v0
  = coe
      MAlonzo.Code.Relation.Binary.Properties.Poset.du_'8805''45'isPartialOrder_142
      (coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v0))
-- Relation.Binary.Properties.TotalOrder.PosetProperties.converse-isPreorder
d_converse'45'isPreorder_182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_converse'45'isPreorder_182 ~v0 ~v1 ~v2 v3
  = du_converse'45'isPreorder_182 v3
du_converse'45'isPreorder_182 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
du_converse'45'isPreorder_182 v0
  = let v1
          = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Properties.Preorder.du_converse'45'isPreorder_78
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_preorder_344 (coe v1)))
-- Relation.Binary.Properties.TotalOrder.PosetProperties.≥-poset
d_'8805''45'poset_184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
d_'8805''45'poset_184 ~v0 ~v1 ~v2 v3 = du_'8805''45'poset_184 v3
du_'8805''45'poset_184 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
du_'8805''45'poset_184 v0
  = coe
      MAlonzo.Code.Relation.Binary.Properties.Poset.du_'8805''45'poset_144
      (coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v0))
-- Relation.Binary.Properties.TotalOrder.PosetProperties.converse-preorder
d_converse'45'preorder_186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
d_converse'45'preorder_186 ~v0 ~v1 ~v2 v3
  = du_converse'45'preorder_186 v3
du_converse'45'preorder_186 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
du_converse'45'preorder_186 v0
  = let v1
          = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Properties.Preorder.du_converse'45'preorder_80
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_preorder_344 (coe v1)))
-- Relation.Binary.Properties.TotalOrder.PosetProperties.refl
d_refl_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny
d_refl_188 ~v0 ~v1 ~v2 v3 = du_refl_188 v3
du_refl_188 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny
du_refl_188 v0
  = let v1
          = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Relation.Binary.Properties.Poset.du_'8805''45'poset_144
                 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Relation.Binary.Bundles.du_preorder_344 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_refl_98
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_154 (coe v3)))))
-- Relation.Binary.Properties.TotalOrder.PosetProperties.reflexive
d_reflexive_190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_190 ~v0 ~v1 ~v2 v3 = du_reflexive_190 v3
du_reflexive_190 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_reflexive_190 v0
  = let v1
          = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Relation.Binary.Properties.Poset.du_'8805''45'poset_144
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_336
                  (coe v2)))))
-- Relation.Binary.Properties.TotalOrder.PosetProperties.trans
d_trans_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_192 ~v0 ~v1 ~v2 v3 = du_trans_192 v3
du_trans_192 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_192 v0
  = let v1
          = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Relation.Binary.Properties.Poset.du_'8805''45'poset_144
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_84
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_336
                  (coe v2)))))
-- Relation.Binary.Properties.TotalOrder.PosetProperties.≰-respʳ-≈
d_'8816''45'resp'691''45''8776'_194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8816''45'resp'691''45''8776'_194 = erased
-- Relation.Binary.Properties.TotalOrder.PosetProperties.≰-respˡ-≈
d_'8816''45'resp'737''45''8776'_196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8816''45'resp'737''45''8776'_196 = erased
-- Relation.Binary.Properties.TotalOrder.decTotalOrder
d_decTotalOrder_198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866
d_decTotalOrder_198 ~v0 ~v1 ~v2 v3 v4 = du_decTotalOrder_198 v3 v4
du_decTotalOrder_198 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866
du_decTotalOrder_198 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_DecTotalOrder'46'constructor_17849
      (coe
         MAlonzo.Code.Relation.Binary.Structures.C_IsDecTotalOrder'46'constructor_22695
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_786 (coe v0))
         (coe v1)
         (coe
            MAlonzo.Code.Relation.Binary.Consequences.du_total'8743'dec'8658'dec_204
            (let v2
                   = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v0) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_336
                        (coe v2)))))
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_412
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_786 (coe v0))))
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_total_414
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_786 (coe v0)))
            (coe v1)))
-- Relation.Binary.Properties.TotalOrder.≥-isTotalOrder
d_'8805''45'isTotalOrder_202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_404
d_'8805''45'isTotalOrder_202 ~v0 ~v1 ~v2 v3
  = du_'8805''45'isTotalOrder_202 v3
du_'8805''45'isTotalOrder_202 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_404
du_'8805''45'isTotalOrder_202 v0
  = coe
      MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_isTotalOrder_398
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_786 (coe v0))
-- Relation.Binary.Properties.TotalOrder.≥-totalOrder
d_'8805''45'totalOrder_204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764
d_'8805''45'totalOrder_204 ~v0 ~v1 ~v2 v3
  = du_'8805''45'totalOrder_204 v3
du_'8805''45'totalOrder_204 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764
du_'8805''45'totalOrder_204 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_TotalOrder'46'constructor_15747
      (coe du_'8805''45'isTotalOrder_202 (coe v0))
-- Relation.Binary.Properties.TotalOrder._.total
d_total_208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_total_208 ~v0 ~v1 ~v2 v3 = du_total_208 v3
du_total_208 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_total_208 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_total_414
      (coe du_'8805''45'isTotalOrder_202 (coe v0))
-- Relation.Binary.Properties.TotalOrder.≰⇒>
d_'8816''8658''62'_214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8816''8658''62'_214 ~v0 ~v1 ~v2 v3 v4 v5
  = du_'8816''8658''62'_214 v3 v4 v5
du_'8816''8658''62'_214 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8816''8658''62'_214 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Construct.NonStrictToStrict.du_'8816''8658''62'_76
      (let v3
             = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v0) in
       coe
         (let v4
                = coe
                    MAlonzo.Code.Relation.Binary.Bundles.du_preorder_344 (coe v3) in
          coe
            (let v5
                   = coe
                       MAlonzo.Code.Relation.Binary.Bundles.du_setoid_180 (coe v4) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (coe v5))))))
      (let v3
             = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v0) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_336
                  (coe v3)))))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_total_414
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_786 (coe v0)))
      (coe v1) (coe v2)
-- Relation.Binary.Properties.TotalOrder.≰⇒≥
d_'8816''8658''8805'_220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny
d_'8816''8658''8805'_220 ~v0 ~v1 ~v2 v3 v4 v5 ~v6
  = du_'8816''8658''8805'_220 v3 v4 v5
du_'8816''8658''8805'_220 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8816''8658''8805'_220 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe du_'8816''8658''62'_214 v0 v1 v2 erased)
