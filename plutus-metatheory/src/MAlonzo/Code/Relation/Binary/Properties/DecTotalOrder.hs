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

module MAlonzo.Code.Relation.Binary.Properties.DecTotalOrder where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.Irrelevant qualified
import MAlonzo.Code.Data.Sum.Base qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd qualified
import MAlonzo.Code.Relation.Binary.Construct.NonStrictToStrict qualified
import MAlonzo.Code.Relation.Binary.Definitions qualified
import MAlonzo.Code.Relation.Binary.Properties.Poset qualified
import MAlonzo.Code.Relation.Binary.Properties.Preorder qualified
import MAlonzo.Code.Relation.Binary.Properties.TotalOrder qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.Code.Relation.Nullary.Decidable.Core qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Relation.Binary.Properties.DecTotalOrder._._≳_
d__'8819'__28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  AgdaAny -> AgdaAny -> ()
d__'8819'__28 = erased
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties._<_
d__'60'__158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  AgdaAny -> AgdaAny -> ()
d__'60'__158 = erased
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.asym
d_asym_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_asym_160 = erased
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.irrefl
d_irrefl_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irrefl_162 = erased
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.<-isStrictPartialOrder
d_'60''45'isStrictPartialOrder_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
d_'60''45'isStrictPartialOrder_164 ~v0 ~v1 ~v2 v3
  = du_'60''45'isStrictPartialOrder_164 v3
du_'60''45'isStrictPartialOrder_164 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
du_'60''45'isStrictPartialOrder_164 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_948 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Properties.Poset.du_'60''45'isStrictPartialOrder_170
         (coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v1)))
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.<-resp-≈
d_'60''45'resp'45''8776'_166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'45''8776'_166 ~v0 ~v1 ~v2 v3
  = du_'60''45'resp'45''8776'_166 v3
du_'60''45'resp'45''8776'_166 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''45'resp'45''8776'_166 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_948 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_'60''45'resp'45''8776'_308
            (coe
               MAlonzo.Code.Relation.Binary.Properties.Poset.du_'60''45'isStrictPartialOrder_170
               (coe v2))))
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.<-respʳ-≈
d_'60''45'resp'691''45''8776'_168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'691''45''8776'_168 ~v0 ~v1 ~v2 v3
  = du_'60''45'resp'691''45''8776'_168 v3
du_'60''45'resp'691''45''8776'_168 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''45'resp'691''45''8776'_168 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_948 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Relation.Binary.Properties.Poset.du_'60''45'strictPartialOrder_172
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'60''45'resp'691''45''8776'_328
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_578
                  (coe v3)))))
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.<-respˡ-≈
d_'60''45'resp'737''45''8776'_170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'737''45''8776'_170 ~v0 ~v1 ~v2 v3
  = du_'60''45'resp'737''45''8776'_170 v3
du_'60''45'resp'737''45''8776'_170 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''45'resp'737''45''8776'_170 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_948 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Relation.Binary.Properties.Poset.du_'60''45'strictPartialOrder_172
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'60''45'resp'737''45''8776'_330
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_578
                  (coe v3)))))
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.<-strictPartialOrder
d_'60''45'strictPartialOrder_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556
d_'60''45'strictPartialOrder_172 ~v0 ~v1 ~v2 v3
  = du_'60''45'strictPartialOrder_172 v3
du_'60''45'strictPartialOrder_172 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556
du_'60''45'strictPartialOrder_172 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_948 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Properties.Poset.du_'60''45'strictPartialOrder_172
         (coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v1)))
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.trans
d_trans_174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_trans_174 ~v0 ~v1 ~v2 v3 = du_trans_174 v3
du_trans_174 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_trans_174 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_948 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_306
            (coe
               MAlonzo.Code.Relation.Binary.Properties.Poset.du_'60''45'isStrictPartialOrder_170
               (coe v2))))
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.<⇒≉
d_'60''8658''8777'_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''8658''8777'_176 = erased
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.<⇒≱
d_'60''8658''8817'_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''8658''8817'_178 = erased
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.≤⇒≯
d_'8804''8658''8815'_182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8804''8658''8815'_182 = erased
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.≤∧≉⇒<
d_'8804''8743''8777''8658''60'_184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
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
      MAlonzo.Code.Relation.Binary.Properties.Poset.du_'8804''8743''8777''8658''60'_200
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.antisym
d_antisym_186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_186 ~v0 ~v1 ~v2 v3 = du_antisym_186 v3
du_antisym_186 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_antisym_186 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_948 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v1) in
       coe
         (coe
            (\ v3 v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
                 (MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_336
                    (coe v2))
                 v3 v4 v6 v5)))
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.≥-isPartialOrder
d_'8805''45'isPartialOrder_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_'8805''45'isPartialOrder_188 ~v0 ~v1 ~v2 v3
  = du_'8805''45'isPartialOrder_188 v3
du_'8805''45'isPartialOrder_188 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
du_'8805''45'isPartialOrder_188 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_948 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Properties.Poset.du_'8805''45'isPartialOrder_142
         (coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v1)))
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.converse-isPreorder
d_converse'45'isPreorder_190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_converse'45'isPreorder_190 ~v0 ~v1 ~v2 v3
  = du_converse'45'isPreorder_190 v3
du_converse'45'isPreorder_190 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
du_converse'45'isPreorder_190 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_948 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Properties.Preorder.du_converse'45'isPreorder_78
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.du_preorder_344 (coe v2))))
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.≥-isTotalOrder
d_'8805''45'isTotalOrder_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_404
d_'8805''45'isTotalOrder_192 ~v0 ~v1 ~v2 v3
  = du_'8805''45'isTotalOrder_192 v3
du_'8805''45'isTotalOrder_192 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_404
du_'8805''45'isTotalOrder_192 v0
  = coe
      MAlonzo.Code.Relation.Binary.Properties.TotalOrder.du_'8805''45'isTotalOrder_202
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_948 (coe v0))
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.≥-poset
d_'8805''45'poset_194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
d_'8805''45'poset_194 ~v0 ~v1 ~v2 v3 = du_'8805''45'poset_194 v3
du_'8805''45'poset_194 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
du_'8805''45'poset_194 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_948 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Properties.Poset.du_'8805''45'poset_144
         (coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v1)))
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.converse-preorder
d_converse'45'preorder_196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
d_converse'45'preorder_196 ~v0 ~v1 ~v2 v3
  = du_converse'45'preorder_196 v3
du_converse'45'preorder_196 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
du_converse'45'preorder_196 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_948 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Properties.Preorder.du_converse'45'preorder_80
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.du_preorder_344 (coe v2))))
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.refl
d_refl_198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  AgdaAny -> AgdaAny
d_refl_198 ~v0 ~v1 ~v2 v3 = du_refl_198 v3
du_refl_198 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  AgdaAny -> AgdaAny
du_refl_198 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_948 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Relation.Binary.Properties.Poset.du_'8805''45'poset_144
                    (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Relation.Binary.Bundles.du_preorder_344 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_refl_98
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_154 (coe v4))))))
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.reflexive
d_reflexive_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_200 ~v0 ~v1 ~v2 v3 = du_reflexive_200 v3
du_reflexive_200 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_reflexive_200 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_948 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Relation.Binary.Properties.Poset.du_'8805''45'poset_144
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_336
                     (coe v3))))))
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.total
d_total_202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_total_202 ~v0 ~v1 ~v2 v3 = du_total_202 v3
du_total_202 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_total_202 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_948 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_total_414
         (coe
            MAlonzo.Code.Relation.Binary.Properties.TotalOrder.du_'8805''45'isTotalOrder_202
            (coe v1)))
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.≥-totalOrder
d_'8805''45'totalOrder_204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764
d_'8805''45'totalOrder_204 ~v0 ~v1 ~v2 v3
  = du_'8805''45'totalOrder_204 v3
du_'8805''45'totalOrder_204 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764
du_'8805''45'totalOrder_204 v0
  = coe
      MAlonzo.Code.Relation.Binary.Properties.TotalOrder.du_'8805''45'totalOrder_204
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_948 (coe v0))
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.trans
d_trans_206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_206 ~v0 ~v1 ~v2 v3 = du_trans_206 v3
du_trans_206 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_206 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_948 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Relation.Binary.Properties.Poset.du_'8805''45'poset_144
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_84
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_336
                     (coe v3))))))
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.≰-respʳ-≈
d_'8816''45'resp'691''45''8776'_208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8816''45'resp'691''45''8776'_208 = erased
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.≰-respˡ-≈
d_'8816''45'resp'737''45''8776'_210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8816''45'resp'737''45''8776'_210 = erased
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.≰⇒>
d_'8816''8658''62'_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8816''8658''62'_212 ~v0 ~v1 ~v2 v3 = du_'8816''8658''62'_212 v3
du_'8816''8658''62'_212 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8816''8658''62'_212 v0
  = coe
      MAlonzo.Code.Relation.Binary.Properties.TotalOrder.du_'8816''8658''62'_214
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_948 (coe v0))
-- Relation.Binary.Properties.DecTotalOrder.TotalOrderProperties.≰⇒≥
d_'8816''8658''8805'_214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny
d_'8816''8658''8805'_214 ~v0 ~v1 ~v2 v3
  = du_'8816''8658''8805'_214 v3
du_'8816''8658''8805'_214 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny
du_'8816''8658''8805'_214 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Properties.TotalOrder.du_'8816''8658''8805'_220
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_948 (coe v0))
      v1 v2
-- Relation.Binary.Properties.DecTotalOrder.≥-isDecTotalOrder
d_'8805''45'isDecTotalOrder_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_460
d_'8805''45'isDecTotalOrder_216 ~v0 ~v1 ~v2 v3
  = du_'8805''45'isDecTotalOrder_216 v3
du_'8805''45'isDecTotalOrder_216 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_460
du_'8805''45'isDecTotalOrder_216 v0
  = coe
      MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_isDecTotalOrder_450
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isDecTotalOrder_888
         (coe v0))
-- Relation.Binary.Properties.DecTotalOrder.≥-decTotalOrder
d_'8805''45'decTotalOrder_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866
d_'8805''45'decTotalOrder_218 ~v0 ~v1 ~v2 v3
  = du_'8805''45'decTotalOrder_218 v3
du_'8805''45'decTotalOrder_218 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866
du_'8805''45'decTotalOrder_218 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_DecTotalOrder'46'constructor_17849
      (coe du_'8805''45'isDecTotalOrder_216 (coe v0))
-- Relation.Binary.Properties.DecTotalOrder._._≤?_
d__'8804''63'__222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8804''63'__222 ~v0 ~v1 ~v2 v3 = du__'8804''63'__222 v3
du__'8804''63'__222 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8804''63'__222 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d__'8804''63'__474
      (coe du_'8805''45'isDecTotalOrder_216 (coe v0))
-- Relation.Binary.Properties.DecTotalOrder.<-isStrictTotalOrder
d_'60''45'isStrictTotalOrder_224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534
d_'60''45'isStrictTotalOrder_224 ~v0 ~v1 ~v2 v3
  = du_'60''45'isStrictTotalOrder_224 v3
du_'60''45'isStrictTotalOrder_224 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534
du_'60''45'isStrictTotalOrder_224 v0
  = coe
      MAlonzo.Code.Relation.Binary.Construct.NonStrictToStrict.du_'60''45'isStrictTotalOrder'8322'_602
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isDecTotalOrder_888
         (coe v0))
-- Relation.Binary.Properties.DecTotalOrder.<-strictTotalOrder
d_'60''45'strictTotalOrder_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036
d_'60''45'strictTotalOrder_226 ~v0 ~v1 ~v2 v3
  = du_'60''45'strictTotalOrder_226 v3
du_'60''45'strictTotalOrder_226 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036
du_'60''45'strictTotalOrder_226 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_StrictTotalOrder'46'constructor_21059
      (coe du_'60''45'isStrictTotalOrder_224 (coe v0))
-- Relation.Binary.Properties.DecTotalOrder._._≮_
d__'8814'__230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  AgdaAny -> AgdaAny -> ()
d__'8814'__230 = erased
-- Relation.Binary.Properties.DecTotalOrder._.compare
d_compare_232 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
d_compare_232 ~v0 ~v1 ~v2 v3 = du_compare_232 v3
du_compare_232 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
du_compare_232 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_compare_544
      (coe du_'60''45'isStrictTotalOrder_224 (coe v0))
-- Relation.Binary.Properties.DecTotalOrder.≮⇒≥
d_'8814''8658''8805'_238 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny
d_'8814''8658''8805'_238 ~v0 ~v1 ~v2 v3 v4 v5
  = du_'8814''8658''8805'_238 v3 v4 v5
du_'8814''8658''8805'_238 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny
du_'8814''8658''8805'_238 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Construct.NonStrictToStrict.du_'8814''8658''8805'_126
      (let v4
             = coe
                 MAlonzo.Code.Relation.Binary.Bundles.du_decPoset_996 (coe v0) in
       coe
         (let v5
                = coe
                    MAlonzo.Code.Relation.Binary.Bundles.du_decSetoid_520 (coe v4) in
          coe
            (let v6
                   = coe
                       MAlonzo.Code.Relation.Binary.Bundles.du_setoid_108 (coe v5) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (coe v6))))))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d__'8799'__472
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isDecTotalOrder_888
            (coe v0)))
      (let v4
             = coe
                 MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_948 (coe v0) in
       coe
         (let v5
                = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_336
                     (coe v5))))))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_total_414
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isTotalOrder_470
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isDecTotalOrder_888
               (coe v0))))
      (coe v1) (coe v2)
