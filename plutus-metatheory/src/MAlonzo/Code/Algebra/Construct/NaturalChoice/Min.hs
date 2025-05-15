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

module MAlonzo.Code.Algebra.Construct.NaturalChoice.Min where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Algebra.Bundles qualified
import MAlonzo.Code.Algebra.Bundles.Raw qualified
import MAlonzo.Code.Algebra.Construct.NaturalChoice.Base qualified
import MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp qualified
import MAlonzo.Code.Algebra.Structures qualified
import MAlonzo.Code.Data.Sum.Base qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Algebra.Construct.NaturalChoice.Min._.totalPreorder
d_totalPreorder_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222
d_totalPreorder_54 ~v0 ~v1 ~v2 v3 = du_totalPreorder_54 v3
du_totalPreorder_54 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222
du_totalPreorder_54 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0)
-- Algebra.Construct.NaturalChoice.Min._⊓_
d__'8851'__94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'8851'__94 ~v0 ~v1 ~v2 v3 v4 v5 = du__'8851'__94 v3 v4 v5
du__'8851'__94 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'8851'__94 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Relation.Binary.Structures.d_total_414
              (MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_786 (coe v0))
              v1 v2 in
    coe
      (case coe v3 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4 -> coe v1
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4 -> coe v2
         _                                            -> MAlonzo.RTE.mazUnreachableError)
-- Algebra.Construct.NaturalChoice.Min.x≤y⇒x⊓y≈x
d_x'8804'y'8658'x'8851'y'8776'x_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8658'x'8851'y'8776'x_120 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_x'8804'y'8658'x'8851'y'8776'x_120 v3 v4 v5 v6
du_x'8804'y'8658'x'8851'y'8776'x_120 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'y'8658'x'8851'y'8776'x_120 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Relation.Binary.Structures.d_total_414
              (MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_786 (coe v0))
              v1 v2 in
    coe
      (case coe v4 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
           -> let v6
                    = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v0) in
              coe
                (let v7
                       = coe
                           MAlonzo.Code.Relation.Binary.Bundles.du_preorder_344 (coe v6) in
                 coe
                   (coe
                      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                      (MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                         (coe
                            MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_154 (coe v7)))
                      v1))
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
           -> coe
                MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
                (MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_412
                   (coe
                      MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_786 (coe v0)))
                v2 v1 v5 v3
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Algebra.Construct.NaturalChoice.Min.x≤y⇒y⊓x≈x
d_x'8804'y'8658'y'8851'x'8776'x_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8658'y'8851'x'8776'x_150 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_x'8804'y'8658'y'8851'x'8776'x_150 v3 v4 v5 v6
du_x'8804'y'8658'y'8851'x'8776'x_150 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'y'8658'y'8851'x'8776'x_150 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Relation.Binary.Structures.d_total_414
              (MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_786 (coe v0))
              v2 v1 in
    coe
      (case coe v4 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
           -> coe
                MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
                (MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_412
                   (coe
                      MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_786 (coe v0)))
                v2 v1 v5 v3
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
           -> let v6
                    = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v0) in
              coe
                (let v7
                       = coe
                           MAlonzo.Code.Relation.Binary.Bundles.du_preorder_344 (coe v6) in
                 coe
                   (coe
                      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                      (MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                         (coe
                            MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_154 (coe v7)))
                      v1))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Algebra.Construct.NaturalChoice.Min.minOperator
d_minOperator_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98
d_minOperator_176 ~v0 ~v1 ~v2 v3 = du_minOperator_176 v3
du_minOperator_176 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98
du_minOperator_176 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.C_MinOperator'46'constructor_1121
      (coe du__'8851'__94 (coe v0))
      (coe du_x'8804'y'8658'x'8851'y'8776'x_120 (coe v0))
      (coe
         (\ v1 v2 ->
            coe
              du_x'8804'y'8658'y'8851'x'8776'x_150 (coe v0) (coe v2) (coe v1)))
-- Algebra.Construct.NaturalChoice.Min._.mono-≤-distrib-⊓
d_mono'45''8804''45'distrib'45''8851'_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
d_mono'45''8804''45'distrib'45''8851'_180 ~v0 ~v1 ~v2 v3
  = du_mono'45''8804''45'distrib'45''8851'_180 v3
du_mono'45''8804''45'distrib'45''8851'_180 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
du_mono'45''8804''45'distrib'45''8851'_180 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_mono'45''8804''45'distrib'45''8851'_3114
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
      (coe du_minOperator_176 (coe v0))
-- Algebra.Construct.NaturalChoice.Min._.x≤y⇒x⊓z≤y
d_x'8804'y'8658'x'8851'z'8804'y_182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8658'x'8851'z'8804'y_182 ~v0 ~v1 ~v2 v3
  = du_x'8804'y'8658'x'8851'z'8804'y_182 v3
du_x'8804'y'8658'x'8851'z'8804'y_182 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'y'8658'x'8851'z'8804'y_182 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'x'8851'z'8804'y_3160
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
      (coe du_minOperator_176 (coe v0))
-- Algebra.Construct.NaturalChoice.Min._.x≤y⇒z⊓x≤y
d_x'8804'y'8658'z'8851'x'8804'y_184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8658'z'8851'x'8804'y_184 ~v0 ~v1 ~v2 v3
  = du_x'8804'y'8658'z'8851'x'8804'y_184 v3
du_x'8804'y'8658'z'8851'x'8804'y_184 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'y'8658'z'8851'x'8804'y_184 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'z'8851'x'8804'y_3172
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
      (coe du_minOperator_176 (coe v0))
-- Algebra.Construct.NaturalChoice.Min._.x≤y⊓z⇒x≤y
d_x'8804'y'8851'z'8658'x'8804'y_186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8851'z'8658'x'8804'y_186 ~v0 ~v1 ~v2 v3
  = du_x'8804'y'8851'z'8658'x'8804'y_186 v3
du_x'8804'y'8851'z'8658'x'8804'y_186 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'y'8851'z'8658'x'8804'y_186 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'y_3184
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
      (coe du_minOperator_176 (coe v0))
-- Algebra.Construct.NaturalChoice.Min._.x≤y⊓z⇒x≤z
d_x'8804'y'8851'z'8658'x'8804'z_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8851'z'8658'x'8804'z_188 ~v0 ~v1 ~v2 v3
  = du_x'8804'y'8851'z'8658'x'8804'z_188 v3
du_x'8804'y'8851'z'8658'x'8804'z_188 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'y'8851'z'8658'x'8804'z_188 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'z_3198
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
      (coe du_minOperator_176 (coe v0))
-- Algebra.Construct.NaturalChoice.Min._.x⊓y≈x⇒x≤y
d_x'8851'y'8776'x'8658'x'8804'y_190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8851'y'8776'x'8658'x'8804'y_190 ~v0 ~v1 ~v2 v3
  = du_x'8851'y'8776'x'8658'x'8804'y_190 v3
du_x'8851'y'8776'x'8658'x'8804'y_190 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8851'y'8776'x'8658'x'8804'y_190 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'x'8658'x'8804'y_3068
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
      (coe du_minOperator_176 (coe v0))
-- Algebra.Construct.NaturalChoice.Min._.x⊓y≈y⇒y≤x
d_x'8851'y'8776'y'8658'y'8804'x_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8851'y'8776'y'8658'y'8804'x_192 ~v0 ~v1 ~v2 v3
  = du_x'8851'y'8776'y'8658'y'8804'x_192 v3
du_x'8851'y'8776'y'8658'y'8804'x_192 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8851'y'8776'y'8658'y'8804'x_192 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'y'8658'y'8804'x_3100
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
      (coe du_minOperator_176 (coe v0))
-- Algebra.Construct.NaturalChoice.Min._.x⊓y≤x
d_x'8851'y'8804'x_194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_x'8851'y'8804'x_194 ~v0 ~v1 ~v2 v3 = du_x'8851'y'8804'x_194 v3
du_x'8851'y'8804'x_194 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_x'8851'y'8804'x_194 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2808
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
      (coe du_minOperator_176 (coe v0))
-- Algebra.Construct.NaturalChoice.Min._.x⊓y≤y
d_x'8851'y'8804'y_196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_x'8851'y'8804'y_196 ~v0 ~v1 ~v2 v3 = du_x'8851'y'8804'y_196 v3
du_x'8851'y'8804'y_196 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_x'8851'y'8804'y_196 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2834
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
      (coe du_minOperator_176 (coe v0))
-- Algebra.Construct.NaturalChoice.Min._.⊓-assoc
d_'8851''45'assoc_198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'assoc_198 ~v0 ~v1 ~v2 v3 = du_'8851''45'assoc_198 v3
du_'8851''45'assoc_198 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'assoc_198 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'assoc_2944
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
      (coe du_minOperator_176 (coe v0))
-- Algebra.Construct.NaturalChoice.Min._.⊓-band
d_'8851''45'band_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Algebra.Bundles.T_Band_596
d_'8851''45'band_200 ~v0 ~v1 ~v2 v3 = du_'8851''45'band_200 v3
du_'8851''45'band_200 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Algebra.Bundles.T_Band_596
du_'8851''45'band_200 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'band_3052
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
      (coe du_minOperator_176 (coe v0))
-- Algebra.Construct.NaturalChoice.Min._.⊓-comm
d_'8851''45'comm_202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'comm_202 ~v0 ~v1 ~v2 v3 = du_'8851''45'comm_202 v3
du_'8851''45'comm_202 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'comm_202 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'comm_2856
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
      (coe du_minOperator_176 (coe v0))
-- Algebra.Construct.NaturalChoice.Min._.⊓-commutativeSemigroup
d_'8851''45'commutativeSemigroup_204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662
d_'8851''45'commutativeSemigroup_204 ~v0 ~v1 ~v2 v3
  = du_'8851''45'commutativeSemigroup_204 v3
du_'8851''45'commutativeSemigroup_204 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662
du_'8851''45'commutativeSemigroup_204 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'commutativeSemigroup_3054
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
      (coe du_minOperator_176 (coe v0))
-- Algebra.Construct.NaturalChoice.Min._.⊓-cong
d_'8851''45'cong_206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'cong_206 ~v0 ~v1 ~v2 v3 = du_'8851''45'cong_206 v3
du_'8851''45'cong_206 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'cong_206 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong_2930
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
      (coe du_minOperator_176 (coe v0))
-- Algebra.Construct.NaturalChoice.Min._.⊓-congʳ
d_'8851''45'cong'691'_208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'cong'691'_208 ~v0 ~v1 ~v2 v3
  = du_'8851''45'cong'691'_208 v3
du_'8851''45'cong'691'_208 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'cong'691'_208 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong'691'_2920
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
      (coe du_minOperator_176 (coe v0))
-- Algebra.Construct.NaturalChoice.Min._.⊓-congˡ
d_'8851''45'cong'737'_210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'cong'737'_210 ~v0 ~v1 ~v2 v3
  = du_'8851''45'cong'737'_210 v3
du_'8851''45'cong'737'_210 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'cong'737'_210 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong'737'_2882
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
      (coe du_minOperator_176 (coe v0))
-- Algebra.Construct.NaturalChoice.Min._.⊓-glb
d_'8851''45'glb_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'glb_212 ~v0 ~v1 ~v2 v3 = du_'8851''45'glb_212 v3
du_'8851''45'glb_212 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'glb_212 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'glb_3278
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
      (coe du_minOperator_176 (coe v0))
-- Algebra.Construct.NaturalChoice.Min._.⊓-idem
d_'8851''45'idem_214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny
d_'8851''45'idem_214 ~v0 ~v1 ~v2 v3 = du_'8851''45'idem_214 v3
du_'8851''45'idem_214 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny
du_'8851''45'idem_214 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'idem_2984
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
      (coe du_minOperator_176 (coe v0))
-- Algebra.Construct.NaturalChoice.Min._.⊓-identity
d_'8851''45'identity_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45'identity_216 ~v0 ~v1 ~v2 v3 v4 v5
  = du_'8851''45'identity_216 v3 v4 v5
du_'8851''45'identity_216 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8851''45'identity_216 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         (\ v3 ->
            coe
              du_x'8804'y'8658'y'8851'x'8776'x_150 (coe v0) (coe v3) (coe v1)
              (coe v2 v3)))
      (coe
         (\ v3 ->
            coe
              du_x'8804'y'8658'x'8851'y'8776'x_120 (coe v0) (coe v3) (coe v1)
              (coe v2 v3)))
-- Algebra.Construct.NaturalChoice.Min._.⊓-identityʳ
d_'8851''45'identity'691'_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8851''45'identity'691'_218 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_'8851''45'identity'691'_218 v3 v4 v5 v6
du_'8851''45'identity'691'_218 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_'8851''45'identity'691'_218 v0 v1 v2 v3
  = coe
      du_x'8804'y'8658'x'8851'y'8776'x_120 (coe v0) (coe v3) (coe v1)
      (coe v2 v3)
-- Algebra.Construct.NaturalChoice.Min._.⊓-identityˡ
d_'8851''45'identity'737'_220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8851''45'identity'737'_220 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_'8851''45'identity'737'_220 v3 v4 v5 v6
du_'8851''45'identity'737'_220 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_'8851''45'identity'737'_220 v0 v1 v2 v3
  = coe
      du_x'8804'y'8658'y'8851'x'8776'x_150 (coe v0) (coe v3) (coe v1)
      (coe v2 v3)
-- Algebra.Construct.NaturalChoice.Min._.⊓-isBand
d_'8851''45'isBand_222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
d_'8851''45'isBand_222 ~v0 ~v1 ~v2 v3 = du_'8851''45'isBand_222 v3
du_'8851''45'isBand_222 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
du_'8851''45'isBand_222 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isBand_3034
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
      (coe du_minOperator_176 (coe v0))
-- Algebra.Construct.NaturalChoice.Min._.⊓-isCommutativeSemigroup
d_'8851''45'isCommutativeSemigroup_224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_548
d_'8851''45'isCommutativeSemigroup_224 ~v0 ~v1 ~v2 v3
  = du_'8851''45'isCommutativeSemigroup_224 v3
du_'8851''45'isCommutativeSemigroup_224 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_548
du_'8851''45'isCommutativeSemigroup_224 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isCommutativeSemigroup_3036
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
      (coe du_minOperator_176 (coe v0))
-- Algebra.Construct.NaturalChoice.Min._.⊓-isMagma
d_'8851''45'isMagma_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'8851''45'isMagma_226 ~v0 ~v1 ~v2 v3
  = du_'8851''45'isMagma_226 v3
du_'8851''45'isMagma_226 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_'8851''45'isMagma_226 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isMagma_3030
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
      (coe du_minOperator_176 (coe v0))
-- Algebra.Construct.NaturalChoice.Min._.⊓-isMonoid
d_'8851''45'isMonoid_228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_'8851''45'isMonoid_228 ~v0 ~v1 ~v2 v3
  = du_'8851''45'isMonoid_228 v3
du_'8851''45'isMonoid_228 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
du_'8851''45'isMonoid_228 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isMonoid_3042
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
      (coe du_minOperator_176 (coe v0))
-- Algebra.Construct.NaturalChoice.Min._.⊓-isSelectiveMagma
d_'8851''45'isSelectiveMagma_230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_436
d_'8851''45'isSelectiveMagma_230 ~v0 ~v1 ~v2 v3
  = du_'8851''45'isSelectiveMagma_230 v3
du_'8851''45'isSelectiveMagma_230 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_436
du_'8851''45'isSelectiveMagma_230 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3038
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
      (coe du_minOperator_176 (coe v0))
-- Algebra.Construct.NaturalChoice.Min._.⊓-isSemigroup
d_'8851''45'isSemigroup_232 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_'8851''45'isSemigroup_232 ~v0 ~v1 ~v2 v3
  = du_'8851''45'isSemigroup_232 v3
du_'8851''45'isSemigroup_232 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
du_'8851''45'isSemigroup_232 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSemigroup_3032
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
      (coe du_minOperator_176 (coe v0))
-- Algebra.Construct.NaturalChoice.Min._.⊓-magma
d_'8851''45'magma_234 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_68
d_'8851''45'magma_234 ~v0 ~v1 ~v2 v3 = du_'8851''45'magma_234 v3
du_'8851''45'magma_234 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_68
du_'8851''45'magma_234 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'magma_3048
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
      (coe du_minOperator_176 (coe v0))
-- Algebra.Construct.NaturalChoice.Min._.⊓-mono-≤
d_'8851''45'mono'45''8804'_236 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'mono'45''8804'_236 ~v0 ~v1 ~v2 v3
  = du_'8851''45'mono'45''8804'_236 v3
du_'8851''45'mono'45''8804'_236 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'mono'45''8804'_236 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'45''8804'_3206
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
      (coe du_minOperator_176 (coe v0))
-- Algebra.Construct.NaturalChoice.Min._.⊓-monoid
d_'8851''45'monoid_238 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Algebra.Bundles.T_Monoid_882
d_'8851''45'monoid_238 ~v0 ~v1 ~v2 v3 = du_'8851''45'monoid_238 v3
du_'8851''45'monoid_238 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Algebra.Bundles.T_Monoid_882
du_'8851''45'monoid_238 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'monoid_3060
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
      (coe du_minOperator_176 (coe v0))
-- Algebra.Construct.NaturalChoice.Min._.⊓-monoʳ-≤
d_'8851''45'mono'691''45''8804'_240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'mono'691''45''8804'_240 ~v0 ~v1 ~v2 v3
  = du_'8851''45'mono'691''45''8804'_240 v3
du_'8851''45'mono'691''45''8804'_240 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'mono'691''45''8804'_240 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'691''45''8804'_3266
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
      (coe du_minOperator_176 (coe v0))
-- Algebra.Construct.NaturalChoice.Min._.⊓-monoˡ-≤
d_'8851''45'mono'737''45''8804'_242 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'mono'737''45''8804'_242 ~v0 ~v1 ~v2 v3
  = du_'8851''45'mono'737''45''8804'_242 v3
du_'8851''45'mono'737''45''8804'_242 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'mono'737''45''8804'_242 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'737''45''8804'_3256
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
      (coe du_minOperator_176 (coe v0))
-- Algebra.Construct.NaturalChoice.Min._.⊓-rawMagma
d_'8851''45'rawMagma_244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36
d_'8851''45'rawMagma_244 ~v0 ~v1 ~v2 v3
  = du_'8851''45'rawMagma_244 v3
du_'8851''45'rawMagma_244 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36
du_'8851''45'rawMagma_244 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'rawMagma_3046
      (coe du_minOperator_176 (coe v0))
-- Algebra.Construct.NaturalChoice.Min._.⊓-sel
d_'8851''45'sel_246 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8851''45'sel_246 ~v0 ~v1 ~v2 v3 = du_'8851''45'sel_246 v3
du_'8851''45'sel_246 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'8851''45'sel_246 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'sel_2988
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
      (coe du_minOperator_176 (coe v0))
-- Algebra.Construct.NaturalChoice.Min._.⊓-selectiveMagma
d_'8851''45'selectiveMagma_248 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Algebra.Bundles.T_SelectiveMagma_122
d_'8851''45'selectiveMagma_248 ~v0 ~v1 ~v2 v3
  = du_'8851''45'selectiveMagma_248 v3
du_'8851''45'selectiveMagma_248 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Algebra.Bundles.T_SelectiveMagma_122
du_'8851''45'selectiveMagma_248 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'selectiveMagma_3056
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
      (coe du_minOperator_176 (coe v0))
-- Algebra.Construct.NaturalChoice.Min._.⊓-semigroup
d_'8851''45'semigroup_250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
d_'8851''45'semigroup_250 ~v0 ~v1 ~v2 v3
  = du_'8851''45'semigroup_250 v3
du_'8851''45'semigroup_250 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
du_'8851''45'semigroup_250 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'semigroup_3050
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
      (coe du_minOperator_176 (coe v0))
-- Algebra.Construct.NaturalChoice.Min._.⊓-triangulate
d_'8851''45'triangulate_252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'triangulate_252 ~v0 ~v1 ~v2 v3
  = du_'8851''45'triangulate_252 v3
du_'8851''45'triangulate_252 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'triangulate_252 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'triangulate_3292
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_totalPreorder_858 (coe v0))
      (coe du_minOperator_176 (coe v0))
-- Algebra.Construct.NaturalChoice.Min._.⊓-zero
d_'8851''45'zero_254 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45'zero_254 ~v0 ~v1 ~v2 v3 v4 v5
  = du_'8851''45'zero_254 v3 v4 v5
du_'8851''45'zero_254 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8851''45'zero_254 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         (\ v3 ->
            coe
              du_x'8804'y'8658'x'8851'y'8776'x_120 (coe v0) (coe v1) (coe v3)
              (coe v2 v3)))
      (coe
         (\ v3 ->
            coe
              du_x'8804'y'8658'y'8851'x'8776'x_150 (coe v0) (coe v1) (coe v3)
              (coe v2 v3)))
-- Algebra.Construct.NaturalChoice.Min._.⊓-zeroʳ
d_'8851''45'zero'691'_256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8851''45'zero'691'_256 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_'8851''45'zero'691'_256 v3 v4 v5 v6
du_'8851''45'zero'691'_256 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_'8851''45'zero'691'_256 v0 v1 v2 v3
  = coe
      du_x'8804'y'8658'y'8851'x'8776'x_150 (coe v0) (coe v1) (coe v3)
      (coe v2 v3)
-- Algebra.Construct.NaturalChoice.Min._.⊓-zeroˡ
d_'8851''45'zero'737'_258 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8851''45'zero'737'_258 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_'8851''45'zero'737'_258 v3 v4 v5 v6
du_'8851''45'zero'737'_258 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_'8851''45'zero'737'_258 v0 v1 v2 v3
  = coe
      du_x'8804'y'8658'x'8851'y'8776'x_120 (coe v0) (coe v1) (coe v3)
      (coe v2 v3)
