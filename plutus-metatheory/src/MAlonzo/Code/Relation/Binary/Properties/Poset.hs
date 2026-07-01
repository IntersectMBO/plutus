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

module MAlonzo.Code.Relation.Binary.Properties.Poset where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Consequences
import qualified MAlonzo.Code.Relation.Binary.Construct.NonStrictToStrict
import qualified MAlonzo.Code.Relation.Binary.Properties.Preorder
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Relation.Binary.Properties.Poset._._≉_
d__'8777'__22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  AgdaAny -> AgdaAny -> ()
d__'8777'__22 = erased
-- Relation.Binary.Properties.Poset._._∼ᵒ_
d__'8764''7506'__26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  AgdaAny -> AgdaAny -> ()
d__'8764''7506'__26 = erased
-- Relation.Binary.Properties.Poset._._≁_
d__'8769'__28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  AgdaAny -> AgdaAny -> ()
d__'8769'__28 = erased
-- Relation.Binary.Properties.Poset.PreorderProperties.converse-isPreorder
d_converse'45'isPreorder_142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_converse'45'isPreorder_142 ~v0 ~v1 ~v2 v3
  = du_converse'45'isPreorder_142 v3
du_converse'45'isPreorder_142 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
du_converse'45'isPreorder_142 v0
  = coe
      MAlonzo.Code.Relation.Binary.Properties.Preorder.du_converse'45'isPreorder_86
      (coe MAlonzo.Code.Relation.Binary.Bundles.du_preorder_522 (coe v0))
-- Relation.Binary.Properties.Poset.PreorderProperties.converse-preorder
d_converse'45'preorder_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
d_converse'45'preorder_144 ~v0 ~v1 ~v2 v3
  = du_converse'45'preorder_144 v3
du_converse'45'preorder_144 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
du_converse'45'preorder_144 v0
  = coe
      MAlonzo.Code.Relation.Binary.Properties.Preorder.du_converse'45'preorder_88
      (coe MAlonzo.Code.Relation.Binary.Bundles.du_preorder_522 (coe v0))
-- Relation.Binary.Properties.Poset.≥-isPartialOrder
d_'8805''45'isPartialOrder_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_'8805''45'isPartialOrder_150 ~v0 ~v1 ~v2 v3
  = du_'8805''45'isPartialOrder_150 v3
du_'8805''45'isPartialOrder_150 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
du_'8805''45'isPartialOrder_150 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_294
      (coe
         MAlonzo.Code.Relation.Binary.Properties.Preorder.du_converse'45'isPreorder_86
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_preorder_522 (coe v0)))
      (coe
         (\ v1 v2 v3 v4 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
              (MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_514
                 (coe v0))
              v1 v2 v4 v3))
-- Relation.Binary.Properties.Poset.≥-poset
d_'8805''45'poset_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
d_'8805''45'poset_152 ~v0 ~v1 ~v2 v3 = du_'8805''45'poset_152 v3
du_'8805''45'poset_152 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
du_'8805''45'poset_152 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_588
      (coe du_'8805''45'isPartialOrder_150 (coe v0))
-- Relation.Binary.Properties.Poset._.antisym
d_antisym_156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_156 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7
  = du_antisym_156 v3 v4 v5 v6 v7
du_antisym_156 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_antisym_156 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
      (MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_514
         (coe v0))
      v1 v2 v4 v3
-- Relation.Binary.Properties.Poset._.refl
d_refl_158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  AgdaAny -> AgdaAny
d_refl_158 ~v0 ~v1 ~v2 v3 = du_refl_158 v3
du_refl_158 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  AgdaAny -> AgdaAny
du_refl_158 v0
  = let v1 = coe du_'8805''45'poset_152 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Relation.Binary.Bundles.du_preorder_522 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_refl_104
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_164 (coe v2))))
-- Relation.Binary.Properties.Poset._.reflexive
d_reflexive_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_160 ~v0 ~v1 ~v2 v3 = du_reflexive_160 v3
du_reflexive_160 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_reflexive_160 v0
  = let v1 = coe du_'8805''45'poset_152 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_514
               (coe v1))))
-- Relation.Binary.Properties.Poset._.trans
d_trans_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_162 ~v0 ~v1 ~v2 v3 = du_trans_162 v3
du_trans_162 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_162 v0
  = let v1 = coe du_'8805''45'poset_152 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_90
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_514
               (coe v1))))
-- Relation.Binary.Properties.Poset.≰-respˡ-≈
d_'8816''45'resp'737''45''8776'_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8816''45'resp'737''45''8776'_164 = erased
-- Relation.Binary.Properties.Poset.≰-respʳ-≈
d_'8816''45'resp'691''45''8776'_170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8816''45'resp'691''45''8776'_170 = erased
-- Relation.Binary.Properties.Poset._<_
d__'60'__176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  AgdaAny -> AgdaAny -> ()
d__'60'__176 = erased
-- Relation.Binary.Properties.Poset.<-isStrictPartialOrder
d_'60''45'isStrictPartialOrder_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370
d_'60''45'isStrictPartialOrder_178 ~v0 ~v1 ~v2 v3
  = du_'60''45'isStrictPartialOrder_178 v3
du_'60''45'isStrictPartialOrder_178 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370
du_'60''45'isStrictPartialOrder_178 v0
  = coe
      MAlonzo.Code.Relation.Binary.Construct.NonStrictToStrict.du_'60''45'isStrictPartialOrder_444
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_514 (coe v0))
-- Relation.Binary.Properties.Poset.<-strictPartialOrder
d_'60''45'strictPartialOrder_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_760
d_'60''45'strictPartialOrder_180 ~v0 ~v1 ~v2 v3
  = du_'60''45'strictPartialOrder_180 v3
du_'60''45'strictPartialOrder_180 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_760
du_'60''45'strictPartialOrder_180 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_842
      (coe du_'60''45'isStrictPartialOrder_178 (coe v0))
-- Relation.Binary.Properties.Poset._._≁_
d__'8769'__184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  AgdaAny -> AgdaAny -> ()
d__'8769'__184 = erased
-- Relation.Binary.Properties.Poset._.asym
d_asym_186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_asym_186 = erased
-- Relation.Binary.Properties.Poset._.irrefl
d_irrefl_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irrefl_188 = erased
-- Relation.Binary.Properties.Poset._.<-resp-≈
d_'60''45'resp'45''8776'_190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'45''8776'_190 ~v0 ~v1 ~v2 v3
  = du_'60''45'resp'45''8776'_190 v3
du_'60''45'resp'45''8776'_190 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''45'resp'45''8776'_190 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_'60''45'resp'45''8776'_388
      (coe du_'60''45'isStrictPartialOrder_178 (coe v0))
-- Relation.Binary.Properties.Poset._.<-respʳ-≈
d_'60''45'resp'691''45''8776'_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'691''45''8776'_192 ~v0 ~v1 ~v2 v3
  = du_'60''45'resp'691''45''8776'_192 v3
du_'60''45'resp'691''45''8776'_192 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''45'resp'691''45''8776'_192 v0
  = let v1 = coe du_'60''45'strictPartialOrder_180 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'60''45'resp'691''45''8776'_408
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_782
            (coe v1)))
-- Relation.Binary.Properties.Poset._.<-respˡ-≈
d_'60''45'resp'737''45''8776'_194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'737''45''8776'_194 ~v0 ~v1 ~v2 v3
  = du_'60''45'resp'737''45''8776'_194 v3
du_'60''45'resp'737''45''8776'_194 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''45'resp'737''45''8776'_194 v0
  = let v1 = coe du_'60''45'strictPartialOrder_180 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'60''45'resp'737''45''8776'_410
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_782
            (coe v1)))
-- Relation.Binary.Properties.Poset._.trans
d_trans_196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_trans_196 ~v0 ~v1 ~v2 v3 = du_trans_196 v3
du_trans_196 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_trans_196 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_386
      (coe du_'60''45'isStrictPartialOrder_178 (coe v0))
-- Relation.Binary.Properties.Poset.<⇒≉
d_'60''8658''8777'_202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''8658''8777'_202 = erased
-- Relation.Binary.Properties.Poset.≤∧≉⇒<
d_'8804''8743''8777''8658''60'_208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8804''8743''8777''8658''60'_208 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'8804''8743''8777''8658''60'_208
du_'8804''8743''8777''8658''60'_208 ::
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8804''8743''8777''8658''60'_208
  = coe
      MAlonzo.Code.Relation.Binary.Construct.NonStrictToStrict.du_'8804''8743''8777''8658''60'_44
-- Relation.Binary.Properties.Poset.<⇒≱
d_'60''8658''8817'_214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''8658''8817'_214 = erased
-- Relation.Binary.Properties.Poset.≤⇒≯
d_'8804''8658''8815'_220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8804''8658''8815'_220 = erased
-- Relation.Binary.Properties.Poset.≤-dec⇒≈-dec
d_'8804''45'dec'8658''8776''45'dec_222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8804''45'dec'8658''8776''45'dec_222 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_'8804''45'dec'8658''8776''45'dec_222 v3 v4 v5 v6
du_'8804''45'dec'8658''8776''45'dec_222 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8804''45'dec'8658''8776''45'dec_222 v0 v1 v2 v3
  = let v4 = coe v1 v2 v3 in
    coe
      (let v5 = coe v1 v3 v2 in
       coe
         (case coe v4 of
            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
              -> if coe v6
                   then case coe v7 of
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v8
                            -> case coe v5 of
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                   -> if coe v9
                                        then case coe v10 of
                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v11
                                                 -> coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                      (coe v9)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                         (coe
                                                            MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
                                                            (MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_514
                                                               (coe v0))
                                                            v2 v3 v8 v11))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        else coe
                                               seq (coe v10)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                  (coe v9)
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError
                   else coe
                          seq (coe v7)
                          (coe
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                             (coe v6)
                             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Relation.Binary.Properties.Poset.≤-dec⇒isDecPartialOrder
d_'8804''45'dec'8658'isDecPartialOrder_266 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_300
d_'8804''45'dec'8658'isDecPartialOrder_266 ~v0 ~v1 ~v2 v3 v4
  = du_'8804''45'dec'8658'isDecPartialOrder_266 v3 v4
du_'8804''45'dec'8658'isDecPartialOrder_266 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_300
du_'8804''45'dec'8658'isDecPartialOrder_266 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_364
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_514 (coe v0))
      (coe du_'8804''45'dec'8658''8776''45'dec_222 (coe v0) (coe v1))
      (coe v1)
-- Relation.Binary.Properties.Poset.mono⇒cong
d_mono'8658'cong_272 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_mono'8658'cong_272 ~v0 ~v1 ~v2 v3 v4
  = du_mono'8658'cong_272 v3 v4
du_mono'8658'cong_272 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_mono'8658'cong_272 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Consequences.du_mono'8658'cong_278
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_38
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_514
                  (coe v0)))))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_514
               (coe v0))))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_514
            (coe v0)))
      (coe v1)
-- Relation.Binary.Properties.Poset.antimono⇒cong
d_antimono'8658'cong_276 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antimono'8658'cong_276 ~v0 ~v1 ~v2 v3 v4
  = du_antimono'8658'cong_276 v3 v4
du_antimono'8658'cong_276 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_antimono'8658'cong_276 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Consequences.du_antimono'8658'cong_292
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_38
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_514
                  (coe v0)))))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_514
               (coe v0))))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_514
            (coe v0)))
      (coe v1)
