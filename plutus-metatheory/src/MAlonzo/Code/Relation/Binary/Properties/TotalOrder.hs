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

module MAlonzo.Code.Relation.Binary.Properties.TotalOrder where

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
import qualified MAlonzo.Code.Relation.Binary.Consequences
import qualified MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd
import qualified MAlonzo.Code.Relation.Binary.Construct.NonStrictToStrict
import qualified MAlonzo.Code.Relation.Binary.Properties.Poset
import qualified MAlonzo.Code.Relation.Binary.Properties.Preorder
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Relation.Binary.Properties.TotalOrder._._∼ᵒ_
d__'8764''7506'__26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny -> AgdaAny -> ()
d__'8764''7506'__26 = erased
-- Relation.Binary.Properties.TotalOrder._._≁_
d__'8769'__28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny -> AgdaAny -> ()
d__'8769'__28 = erased
-- Relation.Binary.Properties.TotalOrder.PosetProperties._<_
d__'60'__150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny -> AgdaAny -> ()
d__'60'__150 = erased
-- Relation.Binary.Properties.TotalOrder.PosetProperties.asym
d_asym_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_asym_154 = erased
-- Relation.Binary.Properties.TotalOrder.PosetProperties.irrefl
d_irrefl_156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irrefl_156 = erased
-- Relation.Binary.Properties.TotalOrder.PosetProperties.<-isStrictPartialOrder
d_'60''45'isStrictPartialOrder_158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370
d_'60''45'isStrictPartialOrder_158 ~v0 ~v1 ~v2 v3
  = du_'60''45'isStrictPartialOrder_158 v3
du_'60''45'isStrictPartialOrder_158 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370
du_'60''45'isStrictPartialOrder_158 v0
  = coe
      MAlonzo.Code.Relation.Binary.Properties.Poset.du_'60''45'isStrictPartialOrder_178
      (coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_1018 (coe v0))
-- Relation.Binary.Properties.TotalOrder.PosetProperties.<-resp-≈
d_'60''45'resp'45''8776'_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'45''8776'_160 ~v0 ~v1 ~v2 v3
  = du_'60''45'resp'45''8776'_160 v3
du_'60''45'resp'45''8776'_160 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''45'resp'45''8776'_160 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Bundles.du_poset_1018 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_'60''45'resp'45''8776'_388
         (coe
            MAlonzo.Code.Relation.Binary.Properties.Poset.du_'60''45'isStrictPartialOrder_178
            (coe v1)))
-- Relation.Binary.Properties.TotalOrder.PosetProperties.<-respʳ-≈
d_'60''45'resp'691''45''8776'_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'691''45''8776'_162 ~v0 ~v1 ~v2 v3
  = du_'60''45'resp'691''45''8776'_162 v3
du_'60''45'resp'691''45''8776'_162 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''45'resp'691''45''8776'_162 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Bundles.du_poset_1018 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Relation.Binary.Properties.Poset.du_'60''45'strictPartialOrder_180
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'60''45'resp'691''45''8776'_408
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_782
               (coe v2))))
-- Relation.Binary.Properties.TotalOrder.PosetProperties.<-respˡ-≈
d_'60''45'resp'737''45''8776'_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'737''45''8776'_164 ~v0 ~v1 ~v2 v3
  = du_'60''45'resp'737''45''8776'_164 v3
du_'60''45'resp'737''45''8776'_164 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''45'resp'737''45''8776'_164 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Bundles.du_poset_1018 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Relation.Binary.Properties.Poset.du_'60''45'strictPartialOrder_180
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'60''45'resp'737''45''8776'_410
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_782
               (coe v2))))
-- Relation.Binary.Properties.TotalOrder.PosetProperties.<-strictPartialOrder
d_'60''45'strictPartialOrder_166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_760
d_'60''45'strictPartialOrder_166 ~v0 ~v1 ~v2 v3
  = du_'60''45'strictPartialOrder_166 v3
du_'60''45'strictPartialOrder_166 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_760
du_'60''45'strictPartialOrder_166 v0
  = coe
      MAlonzo.Code.Relation.Binary.Properties.Poset.du_'60''45'strictPartialOrder_180
      (coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_1018 (coe v0))
-- Relation.Binary.Properties.TotalOrder.PosetProperties.trans
d_trans_168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_trans_168 ~v0 ~v1 ~v2 v3 = du_trans_168 v3
du_trans_168 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_trans_168 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Bundles.du_poset_1018 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_386
         (coe
            MAlonzo.Code.Relation.Binary.Properties.Poset.du_'60''45'isStrictPartialOrder_178
            (coe v1)))
-- Relation.Binary.Properties.TotalOrder.PosetProperties.<⇒≉
d_'60''8658''8777'_170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''8658''8777'_170 = erased
-- Relation.Binary.Properties.TotalOrder.PosetProperties.<⇒≱
d_'60''8658''8817'_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''8658''8817'_172 = erased
-- Relation.Binary.Properties.TotalOrder.PosetProperties.≤⇒≯
d_'8804''8658''8815'_182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8804''8658''8815'_182 = erased
-- Relation.Binary.Properties.TotalOrder.PosetProperties.≤∧≉⇒<
d_'8804''8743''8777''8658''60'_184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8804''8743''8777''8658''60'_184 ~v0 ~v1 ~v2 ~v3
  = du_'8804''8743''8777''8658''60'_184
du_'8804''8743''8777''8658''60'_184 ::
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8804''8743''8777''8658''60'_184 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Properties.Poset.du_'8804''8743''8777''8658''60'_208
-- Relation.Binary.Properties.TotalOrder.PosetProperties.antisym
d_antisym_186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_186 ~v0 ~v1 ~v2 v3 = du_antisym_186 v3
du_antisym_186 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_antisym_186 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Bundles.du_poset_1018 (coe v0) in
    coe
      (coe
         (\ v2 v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
              (MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_514
                 (coe v1))
              v2 v3 v5 v4))
-- Relation.Binary.Properties.TotalOrder.PosetProperties.≥-isPartialOrder
d_'8805''45'isPartialOrder_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_'8805''45'isPartialOrder_188 ~v0 ~v1 ~v2 v3
  = du_'8805''45'isPartialOrder_188 v3
du_'8805''45'isPartialOrder_188 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
du_'8805''45'isPartialOrder_188 v0
  = coe
      MAlonzo.Code.Relation.Binary.Properties.Poset.du_'8805''45'isPartialOrder_150
      (coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_1018 (coe v0))
-- Relation.Binary.Properties.TotalOrder.PosetProperties.converse-isPreorder
d_converse'45'isPreorder_190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_converse'45'isPreorder_190 ~v0 ~v1 ~v2 v3
  = du_converse'45'isPreorder_190 v3
du_converse'45'isPreorder_190 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
du_converse'45'isPreorder_190 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Bundles.du_poset_1018 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Properties.Preorder.du_converse'45'isPreorder_86
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_preorder_522 (coe v1)))
-- Relation.Binary.Properties.TotalOrder.PosetProperties.≥-poset
d_'8805''45'poset_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
d_'8805''45'poset_192 ~v0 ~v1 ~v2 v3 = du_'8805''45'poset_192 v3
du_'8805''45'poset_192 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
du_'8805''45'poset_192 v0
  = coe
      MAlonzo.Code.Relation.Binary.Properties.Poset.du_'8805''45'poset_152
      (coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_1018 (coe v0))
-- Relation.Binary.Properties.TotalOrder.PosetProperties.converse-preorder
d_converse'45'preorder_194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
d_converse'45'preorder_194 ~v0 ~v1 ~v2 v3
  = du_converse'45'preorder_194 v3
du_converse'45'preorder_194 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
du_converse'45'preorder_194 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Bundles.du_poset_1018 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Properties.Preorder.du_converse'45'preorder_88
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_preorder_522 (coe v1)))
-- Relation.Binary.Properties.TotalOrder.PosetProperties.refl
d_refl_196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny -> AgdaAny
d_refl_196 ~v0 ~v1 ~v2 v3 = du_refl_196 v3
du_refl_196 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny -> AgdaAny
du_refl_196 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Bundles.du_poset_1018 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Relation.Binary.Properties.Poset.du_'8805''45'poset_152
                 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Relation.Binary.Bundles.du_preorder_522 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_refl_104
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_164 (coe v3)))))
-- Relation.Binary.Properties.TotalOrder.PosetProperties.reflexive
d_reflexive_198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_198 ~v0 ~v1 ~v2 v3 = du_reflexive_198 v3
du_reflexive_198 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_reflexive_198 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Bundles.du_poset_1018 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Relation.Binary.Properties.Poset.du_'8805''45'poset_152
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_514
                  (coe v2)))))
-- Relation.Binary.Properties.TotalOrder.PosetProperties.trans
d_trans_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_200 ~v0 ~v1 ~v2 v3 = du_trans_200 v3
du_trans_200 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_200 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Bundles.du_poset_1018 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Relation.Binary.Properties.Poset.du_'8805''45'poset_152
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_90
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_514
                  (coe v2)))))
-- Relation.Binary.Properties.TotalOrder.PosetProperties.≰-respʳ-≈
d_'8816''45'resp'691''45''8776'_202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8816''45'resp'691''45''8776'_202 = erased
-- Relation.Binary.Properties.TotalOrder.PosetProperties.≰-respˡ-≈
d_'8816''45'resp'737''45''8776'_204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8816''45'resp'737''45''8776'_204 = erased
-- Relation.Binary.Properties.TotalOrder.decTotalOrder
d_decTotalOrder_206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098
d_decTotalOrder_206 ~v0 ~v1 ~v2 v3 v4 = du_decTotalOrder_206 v3 v4
du_decTotalOrder_206 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098
du_decTotalOrder_206 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_1272
      (coe
         MAlonzo.Code.Relation.Binary.Structures.C_constructor_618
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_1008 (coe v0))
         (coe v1)
         (coe
            MAlonzo.Code.Relation.Binary.Consequences.du_total'8743'dec'8658'dec_206
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_496
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_1008
                        (coe v0)))))
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_496
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_1008
                     (coe v0))))
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_total_498
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_1008 (coe v0)))
            (coe v1)))
-- Relation.Binary.Properties.TotalOrder.≥-isTotalOrder
d_'8805''45'isTotalOrder_210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_488
d_'8805''45'isTotalOrder_210 ~v0 ~v1 ~v2 v3
  = du_'8805''45'isTotalOrder_210 v3
du_'8805''45'isTotalOrder_210 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_488
du_'8805''45'isTotalOrder_210 v0
  = coe
      MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_isTotalOrder_398
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_1008 (coe v0))
-- Relation.Binary.Properties.TotalOrder.≥-totalOrder
d_'8805''45'totalOrder_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986
d_'8805''45'totalOrder_212 ~v0 ~v1 ~v2 v3
  = du_'8805''45'totalOrder_212 v3
du_'8805''45'totalOrder_212 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986
du_'8805''45'totalOrder_212 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_1090
      (coe du_'8805''45'isTotalOrder_210 (coe v0))
-- Relation.Binary.Properties.TotalOrder._.total
d_total_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_total_216 ~v0 ~v1 ~v2 v3 = du_total_216 v3
du_total_216 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_total_216 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_total_498
      (coe du_'8805''45'isTotalOrder_210 (coe v0))
-- Relation.Binary.Properties.TotalOrder.≰⇒>
d_'8816''8658''62'_222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8816''8658''62'_222 ~v0 ~v1 ~v2 v3 v4 v5
  = du_'8816''8658''62'_222 v3 v4 v5
du_'8816''8658''62'_222 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8816''8658''62'_222 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Construct.NonStrictToStrict.du_'8816''8658''62'_76
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_38
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_496
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_1008
                     (coe v0))))))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_496
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_1008
                  (coe v0)))))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_total_498
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_1008 (coe v0)))
      (coe v1) (coe v2)
-- Relation.Binary.Properties.TotalOrder.≰⇒≥
d_'8816''8658''8805'_228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny
d_'8816''8658''8805'_228 ~v0 ~v1 ~v2 v3 v4 v5 ~v6
  = du_'8816''8658''8805'_228 v3 v4 v5
du_'8816''8658''8805'_228 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8816''8658''8805'_228 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe du_'8816''8658''62'_222 v0 v1 v2 erased)
