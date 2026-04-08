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

module MAlonzo.Code.Data.List.Extrema.Core where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Construct.LiftedChoice
import qualified MAlonzo.Code.Algebra.Construct.NaturalChoice.Base
import qualified MAlonzo.Code.Algebra.Construct.NaturalChoice.Max
import qualified MAlonzo.Code.Algebra.Construct.NaturalChoice.Min
import qualified MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd
import qualified MAlonzo.Code.Relation.Binary.Construct.NonStrictToStrict
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Data.List.Extrema.Core._._<_
d__'60'__104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny -> AgdaAny -> ()
d__'60'__104 = erased
-- Data.List.Extrema.Core._._⊓_
d__'8851'__124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'8851'__124 ~v0 ~v1 ~v2 v3 = du__'8851'__124 v3
du__'8851'__124 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'8851'__124 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Min.du__'8851'__102
      (coe v0)
-- Data.List.Extrema.Core.<-transʳ
d_'60''45'trans'691'_138 ::
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
d_'60''45'trans'691'_138 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_'60''45'trans'691'_138 v3 v4 v5 v6
du_'60''45'trans'691'_138 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''45'trans'691'_138 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Construct.NonStrictToStrict.du_'8804''45''60''45'trans_274
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_90
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
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_496
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_1008
                  (coe v0)))))
      (coe v1) (coe v2) (coe v3)
-- Data.List.Extrema.Core.<-transˡ
d_'60''45'trans'737'_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'trans'737'_140 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_'60''45'trans'737'_140 v3 v4 v5 v6
du_'60''45'trans'737'_140 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''45'trans'737'_140 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Construct.NonStrictToStrict.du_'60''45''8804''45'trans_256
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
         MAlonzo.Code.Relation.Binary.Structures.d_trans_90
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
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_112
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_496
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_1008
                  (coe v0)))))
      (coe v1) (coe v2) (coe v3)
-- Data.List.Extrema.Core._.lemma₁
d_lemma'8321'_156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lemma'8321'_156 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11
  = du_lemma'8321'_156 v3 v6 v7 v8 v9 v10 v11
du_lemma'8321'_156 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_lemma'8321'_156 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_90
      (MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_496
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_1008
               (coe v0))))
      (coe v1 v3) (coe v1 v2) v4
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'y'8658'y'8804'x_3216
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_1088
            (coe v0))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Min.du_minOperator_184
            (coe v0))
         (coe v1 v2) (coe v1 v3) (coe v6))
      v5
-- Data.List.Extrema.Core._.lemma₂
d_lemma'8322'_168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lemma'8322'_168 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11
  = du_lemma'8322'_168 v3 v6 v7 v8 v9 v10 v11
du_lemma'8322'_168 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_lemma'8322'_168 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_90
      (MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_496
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_1008
               (coe v0))))
      (coe v1 v2) (coe v1 v3) v4
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'x'8658'x'8804'y_3184
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_1088
            (coe v0))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Min.du_minOperator_184
            (coe v0))
         (coe v1 v2) (coe v1 v3) (coe v6))
      v5
-- Data.List.Extrema.Core._.lemma₃
d_lemma'8323'_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lemma'8323'_180 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11
  = du_lemma'8323'_180 v3 v6 v7 v8 v9 v10 v11
du_lemma'8323'_180 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_lemma'8323'_180 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_'60''45'trans'691'_138 v0 (coe v1 v3) (coe v1 v2) v4
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'y'8658'y'8804'x_3216
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_1088
            (coe v0))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Min.du_minOperator_184
            (coe v0))
         (coe v1 v2) (coe v1 v3) (coe v6))
      v5
-- Data.List.Extrema.Core._.lemma₄
d_lemma'8324'_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lemma'8324'_192 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11
  = du_lemma'8324'_192 v3 v6 v7 v8 v9 v10 v11
du_lemma'8324'_192 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_lemma'8324'_192 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_'60''45'trans'691'_138 v0 (coe v1 v2) (coe v1 v3) v4
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'x'8658'x'8804'y_3184
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_1088
            (coe v0))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Min.du_minOperator_184
            (coe v0))
         (coe v1 v2) (coe v1 v3) (coe v6))
      v5
-- Data.List.Extrema.Core.⊓ᴸ
d_'8851''7480'_198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''7480'_198 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_'8851''7480'_198 v3
du_'8851''7480'_198 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''7480'_198 v0
  = coe
      MAlonzo.Code.Algebra.Construct.LiftedChoice.du_Lift_30
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'sel_3104
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_1088
            (coe v0))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Min.du_minOperator_184
            (coe v0)))
-- Data.List.Extrema.Core.⊔ᴸ
d_'8852''7480'_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_'8852''7480'_200 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_'8852''7480'_200 v3
du_'8852''7480'_200 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_'8852''7480'_200 v0
  = coe
      MAlonzo.Code.Algebra.Construct.LiftedChoice.du_Lift_30
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'sel_3104
         (coe
            MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_1088
               (coe v0)))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Max.du_maxOperator_194
               (coe v0))))
-- Data.List.Extrema.Core.⊓ᴸ-sel
d_'8851''7480''45'sel_204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8851''7480''45'sel_204 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6
  = du_'8851''7480''45'sel_204 v3 v6
du_'8851''7480''45'sel_204 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'8851''7480''45'sel_204 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.LiftedChoice.du_sel'45''8801'_130
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3154
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_1088
            (coe v0))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Min.du_minOperator_184
            (coe v0)))
      (coe v1)
-- Data.List.Extrema.Core.⊓ᴸ-presᵒ-≤v
d_'8851''7480''45'pres'7506''45''8804'v_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_'8851''7480''45'pres'7506''45''8804'v_216 ~v0 ~v1 ~v2 v3 ~v4 ~v5
                                            v6 v7
  = du_'8851''7480''45'pres'7506''45''8804'v_216 v3 v6 v7
du_'8851''7480''45'pres'7506''45''8804'v_216 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_'8851''7480''45'pres'7506''45''8804'v_216 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Construct.LiftedChoice.du_preserves'7506'_400
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3154
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_1088
            (coe v0))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Min.du_minOperator_184
            (coe v0)))
      (coe v1)
      (coe
         (\ v3 v4 ->
            coe
              du_lemma'8321'_156 (coe v0) (coe v1) (coe v3) (coe v4) (coe v2)))
      (coe
         (\ v3 v4 ->
            coe
              du_lemma'8322'_168 (coe v0) (coe v1) (coe v3) (coe v4) (coe v2)))
-- Data.List.Extrema.Core.⊓ᴸ-presᵒ-<v
d_'8851''7480''45'pres'7506''45''60'v_228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''7480''45'pres'7506''45''60'v_228 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6
                                          v7
  = du_'8851''7480''45'pres'7506''45''60'v_228 v3 v6 v7
du_'8851''7480''45'pres'7506''45''60'v_228 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8851''7480''45'pres'7506''45''60'v_228 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Construct.LiftedChoice.du_preserves'7506'_400
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3154
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_1088
            (coe v0))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Min.du_minOperator_184
            (coe v0)))
      (coe v1)
      (coe
         (\ v3 v4 ->
            coe
              du_lemma'8323'_180 (coe v0) (coe v1) (coe v3) (coe v4) (coe v2)))
      (coe
         (\ v3 v4 ->
            coe
              du_lemma'8324'_192 (coe v0) (coe v1) (coe v3) (coe v4) (coe v2)))
-- Data.List.Extrema.Core.⊓ᴸ-presᵇ-v≤
d_'8851''7480''45'pres'7495''45'v'8804'_240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''7480''45'pres'7495''45'v'8804'_240 ~v0 ~v1 ~v2 v3 ~v4 ~v5
                                            v6 ~v7 v8 v9
  = du_'8851''7480''45'pres'7495''45'v'8804'_240 v3 v6 v8 v9
du_'8851''7480''45'pres'7495''45'v'8804'_240 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''7480''45'pres'7495''45'v'8804'_240 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Construct.LiftedChoice.du_preserves'7495'_520
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3154
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_1088
            (coe v0))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Min.du_minOperator_184
            (coe v0)))
      (coe v1) (coe v2) (coe v3)
-- Data.List.Extrema.Core.⊓ᴸ-presᵇ-v<
d_'8851''7480''45'pres'7495''45'v'60'_256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''7480''45'pres'7495''45'v'60'_256 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6
                                          ~v7 v8 v9
  = du_'8851''7480''45'pres'7495''45'v'60'_256 v3 v6 v8 v9
du_'8851''7480''45'pres'7495''45'v'60'_256 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8851''7480''45'pres'7495''45'v'60'_256 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Construct.LiftedChoice.du_preserves'7495'_520
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3154
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_1088
            (coe v0))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Min.du_minOperator_184
            (coe v0)))
      (coe v1) (coe v2) (coe v3)
-- Data.List.Extrema.Core.⊓ᴸ-forcesᵇ-v≤
d_'8851''7480''45'forces'7495''45'v'8804'_272 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''7480''45'forces'7495''45'v'8804'_272 ~v0 ~v1 ~v2 v3 ~v4
                                              ~v5 v6 v7
  = du_'8851''7480''45'forces'7495''45'v'8804'_272 v3 v6 v7
du_'8851''7480''45'forces'7495''45'v'8804'_272 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8851''7480''45'forces'7495''45'v'8804'_272 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Construct.LiftedChoice.du_forces'7495'_562
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3154
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_1088
            (coe v0))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Min.du_minOperator_184
            (coe v0)))
      (coe v1)
      (coe
         (\ v3 v4 v5 v6 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_trans_90
              (MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                 (coe
                    MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_496
                    (coe
                       MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_1008
                       (coe v0))))
              v2 (coe v1 v3) (coe v1 v4) v5
              (coe
                 MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'x'8658'x'8804'y_3184
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_1088
                    (coe v0))
                 (coe
                    MAlonzo.Code.Algebra.Construct.NaturalChoice.Min.du_minOperator_184
                    (coe v0))
                 (coe v1 v3) (coe v1 v4) (coe v6))))
      (coe
         (\ v3 v4 v5 v6 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_trans_90
              (MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                 (coe
                    MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_496
                    (coe
                       MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_1008
                       (coe v0))))
              v2 (coe v1 v4) (coe v1 v3) v5
              (coe
                 MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'y'8658'y'8804'x_3216
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_1088
                    (coe v0))
                 (coe
                    MAlonzo.Code.Algebra.Construct.NaturalChoice.Min.du_minOperator_184
                    (coe v0))
                 (coe v1 v3) (coe v1 v4) (coe v6))))
-- Data.List.Extrema.Core.⊔ᴸ-sel
d_'8852''7480''45'sel_288 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8852''7480''45'sel_288 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6
  = du_'8852''7480''45'sel_288 v3 v6
du_'8852''7480''45'sel_288 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'8852''7480''45'sel_288 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.LiftedChoice.du_sel'45''8801'_130
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3154
         (coe
            MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_1088
               (coe v0)))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Max.du_maxOperator_194
               (coe v0))))
      (coe v1)
-- Data.List.Extrema.Core.⊔ᴸ-presᵒ-v≤
d_'8852''7480''45'pres'7506''45'v'8804'_300 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_'8852''7480''45'pres'7506''45'v'8804'_300 ~v0 ~v1 ~v2 v3 ~v4 ~v5
                                            v6 v7
  = du_'8852''7480''45'pres'7506''45'v'8804'_300 v3 v6 v7
du_'8852''7480''45'pres'7506''45'v'8804'_300 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_'8852''7480''45'pres'7506''45'v'8804'_300 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Construct.LiftedChoice.du_preserves'7506'_400
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3154
         (coe
            MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_1088
               (coe v0)))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Max.du_maxOperator_194
               (coe v0))))
      (coe v1)
      (coe
         (\ v3 v4 v5 v6 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_trans_90
              (MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                 (coe
                    MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_496
                    (coe
                       MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_1008
                       (coe v0))))
              v2 (coe v1 v3) (coe v1 v4) v5
              (coe
                 MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'y'8658'y'8804'x_3216
                 (coe
                    MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
                    (coe
                       MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_1088
                       (coe v0)))
                 (coe
                    MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
                    (coe
                       MAlonzo.Code.Algebra.Construct.NaturalChoice.Max.du_maxOperator_194
                       (coe v0)))
                 (coe v1 v3) (coe v1 v4) (coe v6))))
      (coe
         (\ v3 v4 v5 v6 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_trans_90
              (MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                 (coe
                    MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_496
                    (coe
                       MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_1008
                       (coe v0))))
              v2 (coe v1 v4) (coe v1 v3) v5
              (coe
                 MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'x'8658'x'8804'y_3184
                 (coe
                    MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
                    (coe
                       MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_1088
                       (coe v0)))
                 (coe
                    MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
                    (coe
                       MAlonzo.Code.Algebra.Construct.NaturalChoice.Max.du_maxOperator_194
                       (coe v0)))
                 (coe v1 v3) (coe v1 v4) (coe v6))))
-- Data.List.Extrema.Core.⊔ᴸ-presᵒ-v<
d_'8852''7480''45'pres'7506''45'v'60'_322 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8852''7480''45'pres'7506''45'v'60'_322 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6
                                          v7
  = du_'8852''7480''45'pres'7506''45'v'60'_322 v3 v6 v7
du_'8852''7480''45'pres'7506''45'v'60'_322 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8852''7480''45'pres'7506''45'v'60'_322 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Construct.LiftedChoice.du_preserves'7506'_400
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3154
         (coe
            MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_1088
               (coe v0)))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Max.du_maxOperator_194
               (coe v0))))
      (coe v1)
      (coe
         (\ v3 v4 v5 v6 ->
            coe
              du_'60''45'trans'737'_140 v0 v2 (coe v1 v3) (coe v1 v4) v5
              (coe
                 MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'y'8658'y'8804'x_3216
                 (coe
                    MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
                    (coe
                       MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_1088
                       (coe v0)))
                 (coe
                    MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
                    (coe
                       MAlonzo.Code.Algebra.Construct.NaturalChoice.Max.du_maxOperator_194
                       (coe v0)))
                 (coe v1 v3) (coe v1 v4) (coe v6))))
      (coe
         (\ v3 v4 v5 v6 ->
            coe
              du_'60''45'trans'737'_140 v0 v2 (coe v1 v4) (coe v1 v3) v5
              (coe
                 MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'x'8658'x'8804'y_3184
                 (coe
                    MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
                    (coe
                       MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_1088
                       (coe v0)))
                 (coe
                    MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
                    (coe
                       MAlonzo.Code.Algebra.Construct.NaturalChoice.Max.du_maxOperator_194
                       (coe v0)))
                 (coe v1 v3) (coe v1 v4) (coe v6))))
-- Data.List.Extrema.Core.⊔ᴸ-presᵇ-≤v
d_'8852''7480''45'pres'7495''45''8804'v_344 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8852''7480''45'pres'7495''45''8804'v_344 ~v0 ~v1 ~v2 v3 ~v4 ~v5
                                            v6 ~v7 v8 v9
  = du_'8852''7480''45'pres'7495''45''8804'v_344 v3 v6 v8 v9
du_'8852''7480''45'pres'7495''45''8804'v_344 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8852''7480''45'pres'7495''45''8804'v_344 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Construct.LiftedChoice.du_preserves'7495'_520
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3154
         (coe
            MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_1088
               (coe v0)))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Max.du_maxOperator_194
               (coe v0))))
      (coe v1) (coe v2) (coe v3)
-- Data.List.Extrema.Core.⊔ᴸ-presᵇ-<v
d_'8852''7480''45'pres'7495''45''60'v_360 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8852''7480''45'pres'7495''45''60'v_360 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6
                                          ~v7 v8 v9
  = du_'8852''7480''45'pres'7495''45''60'v_360 v3 v6 v8 v9
du_'8852''7480''45'pres'7495''45''60'v_360 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8852''7480''45'pres'7495''45''60'v_360 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Construct.LiftedChoice.du_preserves'7495'_520
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3154
         (coe
            MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_1088
               (coe v0)))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Max.du_maxOperator_194
               (coe v0))))
      (coe v1) (coe v2) (coe v3)
-- Data.List.Extrema.Core.⊔ᴸ-forcesᵇ-≤v
d_'8852''7480''45'forces'7495''45''8804'v_376 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8852''7480''45'forces'7495''45''8804'v_376 ~v0 ~v1 ~v2 v3 ~v4
                                              ~v5 v6 v7
  = du_'8852''7480''45'forces'7495''45''8804'v_376 v3 v6 v7
du_'8852''7480''45'forces'7495''45''8804'v_376 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8852''7480''45'forces'7495''45''8804'v_376 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Construct.LiftedChoice.du_forces'7495'_562
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3154
         (coe
            MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_1088
               (coe v0)))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Max.du_maxOperator_194
               (coe v0))))
      (coe v1)
      (coe
         (\ v3 v4 v5 v6 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_trans_90
              (MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                 (coe
                    MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_496
                    (coe
                       MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_1008
                       (coe v0))))
              (coe v1 v4) (coe v1 v3) v2
              (coe
                 MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'x'8658'x'8804'y_3184
                 (coe
                    MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
                    (coe
                       MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_1088
                       (coe v0)))
                 (coe
                    MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
                    (coe
                       MAlonzo.Code.Algebra.Construct.NaturalChoice.Max.du_maxOperator_194
                       (coe v0)))
                 (coe v1 v3) (coe v1 v4) (coe v6))
              v5))
      (coe
         (\ v3 v4 v5 v6 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_trans_90
              (MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                 (coe
                    MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_496
                    (coe
                       MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_1008
                       (coe v0))))
              (coe v1 v3) (coe v1 v4) v2
              (coe
                 MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'y'8658'y'8804'x_3216
                 (coe
                    MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
                    (coe
                       MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_1088
                       (coe v0)))
                 (coe
                    MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
                    (coe
                       MAlonzo.Code.Algebra.Construct.NaturalChoice.Max.du_maxOperator_194
                       (coe v0)))
                 (coe v1 v3) (coe v1 v4) (coe v6))
              v5))
