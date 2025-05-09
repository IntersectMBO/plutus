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

module MAlonzo.Code.Data.List.Extrema.Core where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Algebra.Construct.LiftedChoice qualified
import MAlonzo.Code.Algebra.Construct.NaturalChoice.Base qualified
import MAlonzo.Code.Algebra.Construct.NaturalChoice.Max qualified
import MAlonzo.Code.Algebra.Construct.NaturalChoice.Min qualified
import MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp qualified
import MAlonzo.Code.Data.Sum.Base qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd qualified
import MAlonzo.Code.Relation.Binary.Construct.NonStrictToStrict qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.List.Extrema.Core._._<_
d__'60'__96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> ()
d__'60'__96 = erased
-- Data.List.Extrema.Core._._⊓_
d__'8851'__192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'8851'__192 ~v0 ~v1 ~v2 v3 = du__'8851'__192 v3
du__'8851'__192 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'8851'__192 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Min.du__'8851'__94
      (coe v0)
-- Data.List.Extrema.Core.<-transʳ
d_'60''45'trans'691'_284 ::
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
d_'60''45'trans'691'_284 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_'60''45'trans'691'_284 v3 v4 v5 v6
du_'60''45'trans'691'_284 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''45'trans'691'_284 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Construct.NonStrictToStrict.du_'8804''45''60''45'trans_274
      (let v4
             = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v0) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_84
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_336
                  (coe v4)))))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_412
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_786 (coe v0))))
      (let v4
             = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v0) in
       coe
         (let v5
                = coe
                    MAlonzo.Code.Relation.Binary.Bundles.du_preorder_344 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_100
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_154 (coe v5)))))
      (coe v1) (coe v2) (coe v3)
-- Data.List.Extrema.Core.<-transˡ
d_'60''45'trans'737'_286 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'trans'737'_286 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_'60''45'trans'737'_286 v3 v4 v5 v6
du_'60''45'trans'737'_286 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''45'trans'737'_286 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Construct.NonStrictToStrict.du_'60''45''8804''45'trans_256
      (let v4
             = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v0) in
       coe
         (let v5
                = coe
                    MAlonzo.Code.Relation.Binary.Bundles.du_preorder_344 (coe v4) in
          coe
            (let v6
                   = coe
                       MAlonzo.Code.Relation.Binary.Bundles.du_setoid_180 (coe v5) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (coe v6))))))
      (let v4
             = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v0) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_84
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_336
                  (coe v4)))))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_412
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_786 (coe v0))))
      (let v4
             = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v0) in
       coe
         (let v5
                = coe
                    MAlonzo.Code.Relation.Binary.Bundles.du_preorder_344 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_106
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_154 (coe v5)))))
      (coe v1) (coe v2) (coe v3)
-- Data.List.Extrema.Core._.lemma₁
d_lemma'8321'_302 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lemma'8321'_302 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11
  = du_lemma'8321'_302 v3 v6 v7 v8 v9 v10 v11
du_lemma'8321'_302 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_lemma'8321'_302 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_84
         (MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_336
               (coe v7)))
         (coe v1 v3) (coe v1 v2) v4
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'y'8658'y'8804'x_3100
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Min.du_minOperator_176
               (coe v0))
            (coe v1 v2) (coe v1 v3) (coe v6))
         v5)
-- Data.List.Extrema.Core._.lemma₂
d_lemma'8322'_314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lemma'8322'_314 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11
  = du_lemma'8322'_314 v3 v6 v7 v8 v9 v10 v11
du_lemma'8322'_314 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_lemma'8322'_314 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_84
         (MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_336
               (coe v7)))
         (coe v1 v2) (coe v1 v3) v4
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'x'8658'x'8804'y_3068
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Min.du_minOperator_176
               (coe v0))
            (coe v1 v2) (coe v1 v3) (coe v6))
         v5)
-- Data.List.Extrema.Core._.lemma₃
d_lemma'8323'_326 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lemma'8323'_326 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11
  = du_lemma'8323'_326 v3 v6 v7 v8 v9 v10 v11
du_lemma'8323'_326 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_lemma'8323'_326 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_'60''45'trans'691'_284 v0 (coe v1 v3) (coe v1 v2) v4
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'y'8658'y'8804'x_3100
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Min.du_minOperator_176
            (coe v0))
         (coe v1 v2) (coe v1 v3) (coe v6))
      v5
-- Data.List.Extrema.Core._.lemma₄
d_lemma'8324'_338 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lemma'8324'_338 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11
  = du_lemma'8324'_338 v3 v6 v7 v8 v9 v10 v11
du_lemma'8324'_338 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_lemma'8324'_338 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_'60''45'trans'691'_284 v0 (coe v1 v2) (coe v1 v3) v4
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'x'8658'x'8804'y_3068
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Min.du_minOperator_176
            (coe v0))
         (coe v1 v2) (coe v1 v3) (coe v6))
      v5
-- Data.List.Extrema.Core.⊓ᴸ
d_'8851''7480'_344 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''7480'_344 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_'8851''7480'_344 v3
du_'8851''7480'_344 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''7480'_344 v0
  = coe
      MAlonzo.Code.Algebra.Construct.LiftedChoice.du_Lift_30
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'sel_2988
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Min.du_minOperator_176
            (coe v0)))
-- Data.List.Extrema.Core.⊔ᴸ
d_'8852''7480'_346 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_'8852''7480'_346 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_'8852''7480'_346 v3
du_'8852''7480'_346 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_'8852''7480'_346 v0
  = coe
      MAlonzo.Code.Algebra.Construct.LiftedChoice.du_Lift_30
      (let v1
             = coe
                 MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858
                 (coe v0) in
       coe
         (let v2
                = coe
                    MAlonzo.Code.Algebra.Construct.NaturalChoice.Max.du_maxOperator_186
                    (coe v0) in
          coe
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'sel_2988
               (coe
                  MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
                  (coe v1))
               (coe
                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
                  (coe v2)))))
-- Data.List.Extrema.Core.⊓ᴸ-sel
d_'8851''7480''45'sel_350 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8851''7480''45'sel_350 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6
  = du_'8851''7480''45'sel_350 v3 v6
du_'8851''7480''45'sel_350 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'8851''7480''45'sel_350 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.LiftedChoice.du_sel'45''8801'_130
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3038
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Min.du_minOperator_176
            (coe v0)))
      (coe v1)
-- Data.List.Extrema.Core.⊓ᴸ-presᵒ-≤v
d_'8851''7480''45'pres'7506''45''8804'v_362 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_'8851''7480''45'pres'7506''45''8804'v_362 ~v0 ~v1 ~v2 v3 ~v4 ~v5
                                            v6 v7
  = du_'8851''7480''45'pres'7506''45''8804'v_362 v3 v6 v7
du_'8851''7480''45'pres'7506''45''8804'v_362 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_'8851''7480''45'pres'7506''45''8804'v_362 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Construct.LiftedChoice.du_preserves'7506'_400
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3038
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Min.du_minOperator_176
            (coe v0)))
      (coe v1)
      (coe
         (\ v3 v4 ->
            coe
              du_lemma'8321'_302 (coe v0) (coe v1) (coe v3) (coe v4) (coe v2)))
      (coe
         (\ v3 v4 ->
            coe
              du_lemma'8322'_314 (coe v0) (coe v1) (coe v3) (coe v4) (coe v2)))
-- Data.List.Extrema.Core.⊓ᴸ-presᵒ-<v
d_'8851''7480''45'pres'7506''45''60'v_374 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''7480''45'pres'7506''45''60'v_374 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6
                                          v7
  = du_'8851''7480''45'pres'7506''45''60'v_374 v3 v6 v7
du_'8851''7480''45'pres'7506''45''60'v_374 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8851''7480''45'pres'7506''45''60'v_374 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Construct.LiftedChoice.du_preserves'7506'_400
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3038
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Min.du_minOperator_176
            (coe v0)))
      (coe v1)
      (coe
         (\ v3 v4 ->
            coe
              du_lemma'8323'_326 (coe v0) (coe v1) (coe v3) (coe v4) (coe v2)))
      (coe
         (\ v3 v4 ->
            coe
              du_lemma'8324'_338 (coe v0) (coe v1) (coe v3) (coe v4) (coe v2)))
-- Data.List.Extrema.Core.⊓ᴸ-presᵇ-v≤
d_'8851''7480''45'pres'7495''45'v'8804'_386 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''7480''45'pres'7495''45'v'8804'_386 ~v0 ~v1 ~v2 v3 ~v4 ~v5
                                            v6 ~v7 v8 v9
  = du_'8851''7480''45'pres'7495''45'v'8804'_386 v3 v6 v8 v9
du_'8851''7480''45'pres'7495''45'v'8804'_386 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''7480''45'pres'7495''45'v'8804'_386 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Construct.LiftedChoice.du_preserves'7495'_520
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3038
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Min.du_minOperator_176
            (coe v0)))
      (coe v1) (coe v2) (coe v3)
-- Data.List.Extrema.Core.⊓ᴸ-presᵇ-v<
d_'8851''7480''45'pres'7495''45'v'60'_402 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''7480''45'pres'7495''45'v'60'_402 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6
                                          ~v7 v8 v9
  = du_'8851''7480''45'pres'7495''45'v'60'_402 v3 v6 v8 v9
du_'8851''7480''45'pres'7495''45'v'60'_402 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8851''7480''45'pres'7495''45'v'60'_402 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Construct.LiftedChoice.du_preserves'7495'_520
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3038
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Min.du_minOperator_176
            (coe v0)))
      (coe v1) (coe v2) (coe v3)
-- Data.List.Extrema.Core.⊓ᴸ-forcesᵇ-v≤
d_'8851''7480''45'forces'7495''45'v'8804'_418 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''7480''45'forces'7495''45'v'8804'_418 ~v0 ~v1 ~v2 v3 ~v4
                                              ~v5 v6 v7
  = du_'8851''7480''45'forces'7495''45'v'8804'_418 v3 v6 v7
du_'8851''7480''45'forces'7495''45'v'8804'_418 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8851''7480''45'forces'7495''45'v'8804'_418 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Construct.LiftedChoice.du_forces'7495'_562
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3038
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Min.du_minOperator_176
            (coe v0)))
      (coe v1)
      (coe
         (\ v3 v4 v5 v6 ->
            let v7
                  = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v0) in
            coe
              (coe
                 MAlonzo.Code.Relation.Binary.Structures.d_trans_84
                 (MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                    (coe
                       MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_336
                       (coe v7)))
                 v2 (coe v1 v3) (coe v1 v4) v5
                 (coe
                    MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'x'8658'x'8804'y_3068
                    (coe
                       MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
                    (coe
                       MAlonzo.Code.Algebra.Construct.NaturalChoice.Min.du_minOperator_176
                       (coe v0))
                    (coe v1 v3) (coe v1 v4) (coe v6)))))
      (coe
         (\ v3 v4 v5 v6 ->
            let v7
                  = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v0) in
            coe
              (coe
                 MAlonzo.Code.Relation.Binary.Structures.d_trans_84
                 (MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                    (coe
                       MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_336
                       (coe v7)))
                 v2 (coe v1 v4) (coe v1 v3) v5
                 (coe
                    MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'y'8658'y'8804'x_3100
                    (coe
                       MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
                    (coe
                       MAlonzo.Code.Algebra.Construct.NaturalChoice.Min.du_minOperator_176
                       (coe v0))
                    (coe v1 v3) (coe v1 v4) (coe v6)))))
-- Data.List.Extrema.Core.⊔ᴸ-sel
d_'8852''7480''45'sel_434 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8852''7480''45'sel_434 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6
  = du_'8852''7480''45'sel_434 v3 v6
du_'8852''7480''45'sel_434 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'8852''7480''45'sel_434 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.LiftedChoice.du_sel'45''8801'_130
      (let v2
             = coe
                 MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858
                 (coe v0) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Construct.NaturalChoice.Max.du_maxOperator_186
                    (coe v0) in
          coe
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3038
               (coe
                  MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
                  (coe v2))
               (coe
                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
                  (coe v3)))))
      (coe v1)
-- Data.List.Extrema.Core.⊔ᴸ-presᵒ-v≤
d_'8852''7480''45'pres'7506''45'v'8804'_446 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_'8852''7480''45'pres'7506''45'v'8804'_446 ~v0 ~v1 ~v2 v3 ~v4 ~v5
                                            v6 v7
  = du_'8852''7480''45'pres'7506''45'v'8804'_446 v3 v6 v7
du_'8852''7480''45'pres'7506''45'v'8804'_446 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_'8852''7480''45'pres'7506''45'v'8804'_446 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Construct.LiftedChoice.du_preserves'7506'_400
      (let v3
             = coe
                 MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858
                 (coe v0) in
       coe
         (let v4
                = coe
                    MAlonzo.Code.Algebra.Construct.NaturalChoice.Max.du_maxOperator_186
                    (coe v0) in
          coe
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3038
               (coe
                  MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
                  (coe v3))
               (coe
                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
                  (coe v4)))))
      (coe v1)
      (coe
         (\ v3 v4 v5 v6 ->
            let v7
                  = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v0) in
            coe
              (coe
                 MAlonzo.Code.Relation.Binary.Structures.d_trans_84
                 (MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                    (coe
                       MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_336
                       (coe v7)))
                 v2 (coe v1 v3) (coe v1 v4) v5
                 (let v8
                        = coe
                            MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858
                            (coe v0) in
                  coe
                    (let v9
                           = coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Max.du_maxOperator_186
                               (coe v0) in
                     coe
                       (coe
                          MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'y'8658'y'8804'x_3100
                          (coe
                             MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
                             (coe v8))
                          (coe
                             MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
                             (coe v9))
                          (coe v1 v3) (coe v1 v4) (coe v6)))))))
      (coe
         (\ v3 v4 v5 v6 ->
            let v7
                  = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v0) in
            coe
              (coe
                 MAlonzo.Code.Relation.Binary.Structures.d_trans_84
                 (MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                    (coe
                       MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_336
                       (coe v7)))
                 v2 (coe v1 v4) (coe v1 v3) v5
                 (let v8
                        = coe
                            MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858
                            (coe v0) in
                  coe
                    (let v9
                           = coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Max.du_maxOperator_186
                               (coe v0) in
                     coe
                       (coe
                          MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'x'8658'x'8804'y_3068
                          (coe
                             MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
                             (coe v8))
                          (coe
                             MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
                             (coe v9))
                          (coe v1 v3) (coe v1 v4) (coe v6)))))))
-- Data.List.Extrema.Core.⊔ᴸ-presᵒ-v<
d_'8852''7480''45'pres'7506''45'v'60'_468 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8852''7480''45'pres'7506''45'v'60'_468 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6
                                          v7
  = du_'8852''7480''45'pres'7506''45'v'60'_468 v3 v6 v7
du_'8852''7480''45'pres'7506''45'v'60'_468 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8852''7480''45'pres'7506''45'v'60'_468 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Construct.LiftedChoice.du_preserves'7506'_400
      (let v3
             = coe
                 MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858
                 (coe v0) in
       coe
         (let v4
                = coe
                    MAlonzo.Code.Algebra.Construct.NaturalChoice.Max.du_maxOperator_186
                    (coe v0) in
          coe
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3038
               (coe
                  MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
                  (coe v3))
               (coe
                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
                  (coe v4)))))
      (coe v1)
      (coe
         (\ v3 v4 v5 v6 ->
            coe
              du_'60''45'trans'737'_286 v0 v2 (coe v1 v3) (coe v1 v4) v5
              (let v7
                     = coe
                         MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858
                         (coe v0) in
               coe
                 (let v8
                        = coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Max.du_maxOperator_186
                            (coe v0) in
                  coe
                    (coe
                       MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'y'8658'y'8804'x_3100
                       (coe
                          MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
                          (coe v7))
                       (coe
                          MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
                          (coe v8))
                       (coe v1 v3) (coe v1 v4) (coe v6))))))
      (coe
         (\ v3 v4 v5 v6 ->
            coe
              du_'60''45'trans'737'_286 v0 v2 (coe v1 v4) (coe v1 v3) v5
              (let v7
                     = coe
                         MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858
                         (coe v0) in
               coe
                 (let v8
                        = coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Max.du_maxOperator_186
                            (coe v0) in
                  coe
                    (coe
                       MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'x'8658'x'8804'y_3068
                       (coe
                          MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
                          (coe v7))
                       (coe
                          MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
                          (coe v8))
                       (coe v1 v3) (coe v1 v4) (coe v6))))))
-- Data.List.Extrema.Core.⊔ᴸ-presᵇ-≤v
d_'8852''7480''45'pres'7495''45''8804'v_490 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8852''7480''45'pres'7495''45''8804'v_490 ~v0 ~v1 ~v2 v3 ~v4 ~v5
                                            v6 ~v7 v8 v9
  = du_'8852''7480''45'pres'7495''45''8804'v_490 v3 v6 v8 v9
du_'8852''7480''45'pres'7495''45''8804'v_490 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8852''7480''45'pres'7495''45''8804'v_490 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Construct.LiftedChoice.du_preserves'7495'_520
      (let v4
             = coe
                 MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858
                 (coe v0) in
       coe
         (let v5
                = coe
                    MAlonzo.Code.Algebra.Construct.NaturalChoice.Max.du_maxOperator_186
                    (coe v0) in
          coe
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3038
               (coe
                  MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
                  (coe v4))
               (coe
                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
                  (coe v5)))))
      (coe v1) (coe v2) (coe v3)
-- Data.List.Extrema.Core.⊔ᴸ-presᵇ-<v
d_'8852''7480''45'pres'7495''45''60'v_506 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8852''7480''45'pres'7495''45''60'v_506 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6
                                          ~v7 v8 v9
  = du_'8852''7480''45'pres'7495''45''60'v_506 v3 v6 v8 v9
du_'8852''7480''45'pres'7495''45''60'v_506 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8852''7480''45'pres'7495''45''60'v_506 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Construct.LiftedChoice.du_preserves'7495'_520
      (let v4
             = coe
                 MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858
                 (coe v0) in
       coe
         (let v5
                = coe
                    MAlonzo.Code.Algebra.Construct.NaturalChoice.Max.du_maxOperator_186
                    (coe v0) in
          coe
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3038
               (coe
                  MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
                  (coe v4))
               (coe
                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
                  (coe v5)))))
      (coe v1) (coe v2) (coe v3)
-- Data.List.Extrema.Core.⊔ᴸ-forcesᵇ-≤v
d_'8852''7480''45'forces'7495''45''8804'v_522 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8852''7480''45'forces'7495''45''8804'v_522 ~v0 ~v1 ~v2 v3 ~v4
                                              ~v5 v6 v7
  = du_'8852''7480''45'forces'7495''45''8804'v_522 v3 v6 v7
du_'8852''7480''45'forces'7495''45''8804'v_522 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8852''7480''45'forces'7495''45''8804'v_522 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Construct.LiftedChoice.du_forces'7495'_562
      (let v3
             = coe
                 MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858
                 (coe v0) in
       coe
         (let v4
                = coe
                    MAlonzo.Code.Algebra.Construct.NaturalChoice.Max.du_maxOperator_186
                    (coe v0) in
          coe
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3038
               (coe
                  MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
                  (coe v3))
               (coe
                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
                  (coe v4)))))
      (coe v1)
      (coe
         (\ v3 v4 v5 v6 ->
            let v7
                  = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v0) in
            coe
              (coe
                 MAlonzo.Code.Relation.Binary.Structures.d_trans_84
                 (MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                    (coe
                       MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_336
                       (coe v7)))
                 (coe v1 v4) (coe v1 v3) v2
                 (let v8
                        = coe
                            MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858
                            (coe v0) in
                  coe
                    (let v9
                           = coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Max.du_maxOperator_186
                               (coe v0) in
                     coe
                       (coe
                          MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'x'8658'x'8804'y_3068
                          (coe
                             MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
                             (coe v8))
                          (coe
                             MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
                             (coe v9))
                          (coe v1 v3) (coe v1 v4) (coe v6))))
                 v5)))
      (coe
         (\ v3 v4 v5 v6 ->
            let v7
                  = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v0) in
            coe
              (coe
                 MAlonzo.Code.Relation.Binary.Structures.d_trans_84
                 (MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                    (coe
                       MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_336
                       (coe v7)))
                 (coe v1 v3) (coe v1 v4) v2
                 (let v8
                        = coe
                            MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858
                            (coe v0) in
                  coe
                    (let v9
                           = coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Max.du_maxOperator_186
                               (coe v0) in
                     coe
                       (coe
                          MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'y'8658'y'8804'x_3100
                          (coe
                             MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
                             (coe v8))
                          (coe
                             MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
                             (coe v9))
                          (coe v1 v3) (coe v1 v4) (coe v6))))
                 v5)))
