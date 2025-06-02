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

module MAlonzo.Code.Relation.Binary.Properties.Poset where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.Irrelevant qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Consequences qualified
import MAlonzo.Code.Relation.Binary.Construct.NonStrictToStrict qualified
import MAlonzo.Code.Relation.Binary.Properties.Preorder qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.Code.Relation.Nullary.Decidable.Core qualified
import MAlonzo.Code.Relation.Nullary.Reflects qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Relation.Binary.Properties.Poset._._≳_
d__'8819'__24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  AgdaAny -> AgdaAny -> ()
d__'8819'__24 = erased
-- Relation.Binary.Properties.Poset._._⋦_
d__'8934'__26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  AgdaAny -> AgdaAny -> ()
d__'8934'__26 = erased
-- Relation.Binary.Properties.Poset._.Eq._≉_
d__'8777'__64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  AgdaAny -> AgdaAny -> ()
d__'8777'__64 = erased
-- Relation.Binary.Properties.Poset.PreorderProperties.converse-isPreorder
d_converse'45'isPreorder_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_converse'45'isPreorder_134 ~v0 ~v1 ~v2 v3
  = du_converse'45'isPreorder_134 v3
du_converse'45'isPreorder_134 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
du_converse'45'isPreorder_134 v0
  = coe
      MAlonzo.Code.Relation.Binary.Properties.Preorder.du_converse'45'isPreorder_78
      (coe MAlonzo.Code.Relation.Binary.Bundles.du_preorder_344 (coe v0))
-- Relation.Binary.Properties.Poset.PreorderProperties.converse-preorder
d_converse'45'preorder_136 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
d_converse'45'preorder_136 ~v0 ~v1 ~v2 v3
  = du_converse'45'preorder_136 v3
du_converse'45'preorder_136 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
du_converse'45'preorder_136 v0
  = coe
      MAlonzo.Code.Relation.Binary.Properties.Preorder.du_converse'45'preorder_80
      (coe MAlonzo.Code.Relation.Binary.Bundles.du_preorder_344 (coe v0))
-- Relation.Binary.Properties.Poset.≥-isPartialOrder
d_'8805''45'isPartialOrder_142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_'8805''45'isPartialOrder_142 ~v0 ~v1 ~v2 v3
  = du_'8805''45'isPartialOrder_142 v3
du_'8805''45'isPartialOrder_142 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
du_'8805''45'isPartialOrder_142 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsPartialOrder'46'constructor_9853
      (coe
         MAlonzo.Code.Relation.Binary.Properties.Preorder.du_converse'45'isPreorder_78
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_preorder_344 (coe v0)))
      (coe
         (\ v1 v2 v3 v4 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
              (MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_336
                 (coe v0))
              v1 v2 v4 v3))
-- Relation.Binary.Properties.Poset.≥-poset
d_'8805''45'poset_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
d_'8805''45'poset_144 ~v0 ~v1 ~v2 v3 = du_'8805''45'poset_144 v3
du_'8805''45'poset_144 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
du_'8805''45'poset_144 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Poset'46'constructor_6389
      (coe du_'8805''45'isPartialOrder_142 (coe v0))
-- Relation.Binary.Properties.Poset._.antisym
d_antisym_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_148 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7
  = du_antisym_148 v3 v4 v5 v6 v7
du_antisym_148 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_antisym_148 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
      (MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_336
         (coe v0))
      v1 v2 v4 v3
-- Relation.Binary.Properties.Poset._.refl
d_refl_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  AgdaAny -> AgdaAny
d_refl_150 ~v0 ~v1 ~v2 v3 = du_refl_150 v3
du_refl_150 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  AgdaAny -> AgdaAny
du_refl_150 v0
  = let v1 = coe du_'8805''45'poset_144 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Relation.Binary.Bundles.du_preorder_344 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_refl_98
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_154 (coe v2))))
-- Relation.Binary.Properties.Poset._.reflexive
d_reflexive_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_152 ~v0 ~v1 ~v2 v3 = du_reflexive_152 v3
du_reflexive_152 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_reflexive_152 v0
  = let v1 = coe du_'8805''45'poset_144 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_336
               (coe v1))))
-- Relation.Binary.Properties.Poset._.trans
d_trans_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_154 ~v0 ~v1 ~v2 v3 = du_trans_154 v3
du_trans_154 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_154 v0
  = let v1 = coe du_'8805''45'poset_144 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_84
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_336
               (coe v1))))
-- Relation.Binary.Properties.Poset.≰-respˡ-≈
d_'8816''45'resp'737''45''8776'_156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8816''45'resp'737''45''8776'_156 = erased
-- Relation.Binary.Properties.Poset.≰-respʳ-≈
d_'8816''45'resp'691''45''8776'_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8816''45'resp'691''45''8776'_162 = erased
-- Relation.Binary.Properties.Poset._<_
d__'60'__168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  AgdaAny -> AgdaAny -> ()
d__'60'__168 = erased
-- Relation.Binary.Properties.Poset.<-isStrictPartialOrder
d_'60''45'isStrictPartialOrder_170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
d_'60''45'isStrictPartialOrder_170 ~v0 ~v1 ~v2 v3
  = du_'60''45'isStrictPartialOrder_170 v3
du_'60''45'isStrictPartialOrder_170 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
du_'60''45'isStrictPartialOrder_170 v0
  = coe
      MAlonzo.Code.Relation.Binary.Construct.NonStrictToStrict.du_'60''45'isStrictPartialOrder_444
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_336 (coe v0))
-- Relation.Binary.Properties.Poset.<-strictPartialOrder
d_'60''45'strictPartialOrder_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556
d_'60''45'strictPartialOrder_172 ~v0 ~v1 ~v2 v3
  = du_'60''45'strictPartialOrder_172 v3
du_'60''45'strictPartialOrder_172 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556
du_'60''45'strictPartialOrder_172 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_StrictPartialOrder'46'constructor_11097
      (coe du_'60''45'isStrictPartialOrder_170 (coe v0))
-- Relation.Binary.Properties.Poset._._≮_
d__'8814'__176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  AgdaAny -> AgdaAny -> ()
d__'8814'__176 = erased
-- Relation.Binary.Properties.Poset._.asym
d_asym_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_asym_178 = erased
-- Relation.Binary.Properties.Poset._.irrefl
d_irrefl_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irrefl_180 = erased
-- Relation.Binary.Properties.Poset._.<-resp-≈
d_'60''45'resp'45''8776'_182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'45''8776'_182 ~v0 ~v1 ~v2 v3
  = du_'60''45'resp'45''8776'_182 v3
du_'60''45'resp'45''8776'_182 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''45'resp'45''8776'_182 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_'60''45'resp'45''8776'_308
      (coe du_'60''45'isStrictPartialOrder_170 (coe v0))
-- Relation.Binary.Properties.Poset._.<-respʳ-≈
d_'60''45'resp'691''45''8776'_184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'691''45''8776'_184 ~v0 ~v1 ~v2 v3
  = du_'60''45'resp'691''45''8776'_184 v3
du_'60''45'resp'691''45''8776'_184 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''45'resp'691''45''8776'_184 v0
  = let v1 = coe du_'60''45'strictPartialOrder_172 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'60''45'resp'691''45''8776'_328
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_578
            (coe v1)))
-- Relation.Binary.Properties.Poset._.<-respˡ-≈
d_'60''45'resp'737''45''8776'_186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'737''45''8776'_186 ~v0 ~v1 ~v2 v3
  = du_'60''45'resp'737''45''8776'_186 v3
du_'60''45'resp'737''45''8776'_186 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''45'resp'737''45''8776'_186 v0
  = let v1 = coe du_'60''45'strictPartialOrder_172 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'60''45'resp'737''45''8776'_330
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_578
            (coe v1)))
-- Relation.Binary.Properties.Poset._.trans
d_trans_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_trans_188 ~v0 ~v1 ~v2 v3 = du_trans_188 v3
du_trans_188 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_trans_188 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_306
      (coe du_'60''45'isStrictPartialOrder_170 (coe v0))
-- Relation.Binary.Properties.Poset.<⇒≉
d_'60''8658''8777'_194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''8658''8777'_194 = erased
-- Relation.Binary.Properties.Poset.≤∧≉⇒<
d_'8804''8743''8777''8658''60'_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8804''8743''8777''8658''60'_200 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'8804''8743''8777''8658''60'_200
du_'8804''8743''8777''8658''60'_200 ::
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8804''8743''8777''8658''60'_200
  = coe
      MAlonzo.Code.Relation.Binary.Construct.NonStrictToStrict.du_'8804''8743''8777''8658''60'_44
-- Relation.Binary.Properties.Poset.<⇒≱
d_'60''8658''8817'_206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''8658''8817'_206 = erased
-- Relation.Binary.Properties.Poset.≤⇒≯
d_'8804''8658''8815'_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8804''8658''8815'_212 = erased
-- Relation.Binary.Properties.Poset.≤-dec⇒≈-dec
d_'8804''45'dec'8658''8776''45'dec_214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8804''45'dec'8658''8776''45'dec_214 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_'8804''45'dec'8658''8776''45'dec_214 v3 v4 v5 v6
du_'8804''45'dec'8658''8776''45'dec_214 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8804''45'dec'8658''8776''45'dec_214 v0 v1 v2 v3
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
                                                            MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
                                                            (MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_336
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
d_'8804''45'dec'8658'isDecPartialOrder_258 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_224
d_'8804''45'dec'8658'isDecPartialOrder_258 ~v0 ~v1 ~v2 v3 v4
  = du_'8804''45'dec'8658'isDecPartialOrder_258 v3 v4
du_'8804''45'dec'8658'isDecPartialOrder_258 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_224
du_'8804''45'dec'8658'isDecPartialOrder_258 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsDecPartialOrder'46'constructor_11683
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_336 (coe v0))
      (coe du_'8804''45'dec'8658''8776''45'dec_214 (coe v0) (coe v1))
      (coe v1)
-- Relation.Binary.Properties.Poset.mono⇒cong
d_mono'8658'cong_264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_mono'8658'cong_264 ~v0 ~v1 ~v2 v3 v4
  = du_mono'8658'cong_264 v3 v4
du_mono'8658'cong_264 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_mono'8658'cong_264 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Consequences.du_mono'8658'cong_276
      (let v2
             = coe
                 MAlonzo.Code.Relation.Binary.Bundles.du_preorder_344 (coe v0) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Relation.Binary.Bundles.du_setoid_180 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v3)))))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_336
               (coe v0))))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_336
            (coe v0)))
      (coe v1)
-- Relation.Binary.Properties.Poset.antimono⇒cong
d_antimono'8658'cong_268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antimono'8658'cong_268 ~v0 ~v1 ~v2 v3 v4
  = du_antimono'8658'cong_268 v3 v4
du_antimono'8658'cong_268 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_antimono'8658'cong_268 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Consequences.du_antimono'8658'cong_290
      (let v2
             = coe
                 MAlonzo.Code.Relation.Binary.Bundles.du_preorder_344 (coe v0) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Relation.Binary.Bundles.du_setoid_180 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v3)))))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_336
               (coe v0))))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_336
            (coe v0)))
      (coe v1)
