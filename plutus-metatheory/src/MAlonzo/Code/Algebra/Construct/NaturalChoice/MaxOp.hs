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

module MAlonzo.Code.Algebra.Construct.NaturalChoice.MaxOp where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Bundles
import qualified MAlonzo.Code.Algebra.Construct.NaturalChoice.Base
import qualified MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd

-- Algebra.Construct.NaturalChoice.MaxOp._._≈_
d__'8776'__30 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__30 = erased
-- Algebra.Construct.NaturalChoice.MaxOp._._≲_
d__'8818'__34 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> ()
d__'8818'__34 = erased
-- Algebra.Construct.NaturalChoice.MaxOp.Min.x≤y⇒x⊓z≤y
d_x'8804'y'8658'x'8851'z'8804'y_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8658'x'8851'z'8804'y_106 ~v0 ~v1 ~v2 v3 v4
  = du_x'8804'y'8658'x'8851'z'8804'y_106 v3 v4
du_x'8804'y'8658'x'8851'z'8804'y_106 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'y'8658'x'8851'z'8804'y_106 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'x'8851'z'8804'y_3276
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.x≤y⇒z⊓x≤y
d_x'8804'y'8658'z'8851'x'8804'y_108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8658'z'8851'x'8804'y_108 ~v0 ~v1 ~v2 v3 v4
  = du_x'8804'y'8658'z'8851'x'8804'y_108 v3 v4
du_x'8804'y'8658'z'8851'x'8804'y_108 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'y'8658'z'8851'x'8804'y_108 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'z'8851'x'8804'y_3288
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.x≤y⊓z⇒x≤y
d_x'8804'y'8851'z'8658'x'8804'y_110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8851'z'8658'x'8804'y_110 ~v0 ~v1 ~v2 v3 v4
  = du_x'8804'y'8851'z'8658'x'8804'y_110 v3 v4
du_x'8804'y'8851'z'8658'x'8804'y_110 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'y'8851'z'8658'x'8804'y_110 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'y_3300
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.x≤y⊓z⇒x≤z
d_x'8804'y'8851'z'8658'x'8804'z_112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8851'z'8658'x'8804'z_112 ~v0 ~v1 ~v2 v3 v4
  = du_x'8804'y'8851'z'8658'x'8804'z_112 v3 v4
du_x'8804'y'8851'z'8658'x'8804'z_112 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'y'8851'z'8658'x'8804'z_112 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'z_3314
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.x⊓y≈x⇒x≤y
d_x'8851'y'8776'x'8658'x'8804'y_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8851'y'8776'x'8658'x'8804'y_114 ~v0 ~v1 ~v2 v3 v4
  = du_x'8851'y'8776'x'8658'x'8804'y_114 v3 v4
du_x'8851'y'8776'x'8658'x'8804'y_114 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8851'y'8776'x'8658'x'8804'y_114 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'x'8658'x'8804'y_3184
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.x⊓y≈y⇒y≤x
d_x'8851'y'8776'y'8658'y'8804'x_116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8851'y'8776'y'8658'y'8804'x_116 ~v0 ~v1 ~v2 v3 v4
  = du_x'8851'y'8776'y'8658'y'8804'x_116 v3 v4
du_x'8851'y'8776'y'8658'y'8804'x_116 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8851'y'8776'y'8658'y'8804'x_116 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'y'8658'y'8804'x_3216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.x⊓y≤x
d_x'8851'y'8804'x_118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_x'8851'y'8804'x_118 ~v0 ~v1 ~v2 v3 v4
  = du_x'8851'y'8804'x_118 v3 v4
du_x'8851'y'8804'x_118 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_x'8851'y'8804'x_118 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2924
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.x⊓y≤y
d_x'8851'y'8804'y_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_x'8851'y'8804'y_120 ~v0 ~v1 ~v2 v3 v4
  = du_x'8851'y'8804'y_120 v3 v4
du_x'8851'y'8804'y_120 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_x'8851'y'8804'y_120 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2950
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-assoc
d_'8851''45'assoc_122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'assoc_122 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'assoc_122 v3 v4
du_'8851''45'assoc_122 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'assoc_122 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'assoc_3060
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-band
d_'8851''45'band_124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Bundles.T_Band_620
d_'8851''45'band_124 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'band_124 v3 v4
du_'8851''45'band_124 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Bundles.T_Band_620
du_'8851''45'band_124 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'band_3168
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-comm
d_'8851''45'comm_126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'comm_126 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'comm_126 v3 v4
du_'8851''45'comm_126 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'comm_126 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'comm_2972
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-commutativeSemigroup
d_'8851''45'commutativeSemigroup_128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_688
d_'8851''45'commutativeSemigroup_128 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'commutativeSemigroup_128 v3 v4
du_'8851''45'commutativeSemigroup_128 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_688
du_'8851''45'commutativeSemigroup_128 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'commutativeSemigroup_3170
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-cong
d_'8851''45'cong_130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'cong_130 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'cong_130 v3 v4
du_'8851''45'cong_130 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'cong_130 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong_3046
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-congʳ
d_'8851''45'cong'691'_132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'cong'691'_132 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'cong'691'_132 v3 v4
du_'8851''45'cong'691'_132 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'cong'691'_132 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong'691'_3036
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-congˡ
d_'8851''45'cong'737'_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'cong'737'_134 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'cong'737'_134 v3 v4
du_'8851''45'cong'737'_134 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'cong'737'_134 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong'737'_2998
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-glb
d_'8851''45'glb_136 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'glb_136 ~v0 ~v1 ~v2 v3 v4 = du_'8851''45'glb_136 v3 v4
du_'8851''45'glb_136 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'glb_136 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'glb_3394
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-idem
d_'8851''45'idem_138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny
d_'8851''45'idem_138 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'idem_138 v3 v4
du_'8851''45'idem_138 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny
du_'8851''45'idem_138 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'idem_3100
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-identity
d_'8851''45'identity_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45'identity_140 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_'8851''45'identity_140 v4 v5 v6
du_'8851''45'identity_140 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8851''45'identity_140 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         (\ v3 ->
            coe
              MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8852'y'8776'y_160
              v0 v1 v3 (coe v2 v3)))
      (coe
         (\ v3 ->
            coe
              MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8852'y'8776'x_166
              v0 v3 v1 (coe v2 v3)))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-identityʳ
d_'8851''45'identity'691'_142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8851''45'identity'691'_142 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_'8851''45'identity'691'_142 v4 v5 v6 v7
du_'8851''45'identity'691'_142 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_'8851''45'identity'691'_142 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8852'y'8776'x_166
      v0 v3 v1 (coe v2 v3)
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-identityˡ
d_'8851''45'identity'737'_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8851''45'identity'737'_144 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_'8851''45'identity'737'_144 v4 v5 v6 v7
du_'8851''45'identity'737'_144 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_'8851''45'identity'737'_144 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8852'y'8776'y_160
      v0 v1 v3 (coe v2 v3)
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-isBand
d_'8851''45'isBand_146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_'8851''45'isBand_146 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'isBand_146 v3 v4
du_'8851''45'isBand_146 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
du_'8851''45'isBand_146 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isBand_3150
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-isCommutativeSemigroup
d_'8851''45'isCommutativeSemigroup_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_'8851''45'isCommutativeSemigroup_148 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'isCommutativeSemigroup_148 v3 v4
du_'8851''45'isCommutativeSemigroup_148 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_'8851''45'isCommutativeSemigroup_148 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isCommutativeSemigroup_3152
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-isMagma
d_'8851''45'isMagma_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'8851''45'isMagma_150 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'isMagma_150 v3 v4
du_'8851''45'isMagma_150 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_'8851''45'isMagma_150 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isMagma_3146
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-isMonoid
d_'8851''45'isMonoid_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'8851''45'isMonoid_152 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'isMonoid_152 v3 v4
du_'8851''45'isMonoid_152 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
du_'8851''45'isMonoid_152 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isMonoid_3158
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-isSelectiveMagma
d_'8851''45'isSelectiveMagma_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450
d_'8851''45'isSelectiveMagma_154 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'isSelectiveMagma_154 v3 v4
du_'8851''45'isSelectiveMagma_154 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450
du_'8851''45'isSelectiveMagma_154 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3154
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-isSemigroup
d_'8851''45'isSemigroup_156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'8851''45'isSemigroup_156 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'isSemigroup_156 v3 v4
du_'8851''45'isSemigroup_156 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_'8851''45'isSemigroup_156 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSemigroup_3148
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-magma
d_'8851''45'magma_158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_74
d_'8851''45'magma_158 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'magma_158 v3 v4
du_'8851''45'magma_158 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_74
du_'8851''45'magma_158 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'magma_3164
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-mono-≤
d_'8851''45'mono'45''8804'_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'mono'45''8804'_160 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'mono'45''8804'_160 v3 v4
du_'8851''45'mono'45''8804'_160 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'mono'45''8804'_160 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'45''8804'_3322
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-monoid
d_'8851''45'monoid_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Algebra.Bundles.T_Monoid_914
d_'8851''45'monoid_162 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'monoid_162 v3 v4
du_'8851''45'monoid_162 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Algebra.Bundles.T_Monoid_914
du_'8851''45'monoid_162 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'monoid_3176
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-monoʳ-≤
d_'8851''45'mono'691''45''8804'_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'mono'691''45''8804'_164 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'mono'691''45''8804'_164 v3 v4
du_'8851''45'mono'691''45''8804'_164 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'mono'691''45''8804'_164 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'691''45''8804'_3382
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-monoˡ-≤
d_'8851''45'mono'737''45''8804'_166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'mono'737''45''8804'_166 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'mono'737''45''8804'_166 v3 v4
du_'8851''45'mono'737''45''8804'_166 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'mono'737''45''8804'_166 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'737''45''8804'_3372
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-sel
d_'8851''45'sel_170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8851''45'sel_170 ~v0 ~v1 ~v2 v3 v4 = du_'8851''45'sel_170 v3 v4
du_'8851''45'sel_170 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'8851''45'sel_170 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'sel_3104
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-selectiveMagma
d_'8851''45'selectiveMagma_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Bundles.T_SelectiveMagma_130
d_'8851''45'selectiveMagma_172 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'selectiveMagma_172 v3 v4
du_'8851''45'selectiveMagma_172 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Bundles.T_SelectiveMagma_130
du_'8851''45'selectiveMagma_172 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'selectiveMagma_3172
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-semigroup
d_'8851''45'semigroup_174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
d_'8851''45'semigroup_174 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'semigroup_174 v3 v4
du_'8851''45'semigroup_174 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
du_'8851''45'semigroup_174 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'semigroup_3166
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-triangulate
d_'8851''45'triangulate_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'triangulate_176 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'triangulate_176 v3 v4
du_'8851''45'triangulate_176 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'triangulate_176 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'triangulate_3408
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-zero
d_'8851''45'zero_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45'zero_178 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_'8851''45'zero_178 v4 v5 v6
du_'8851''45'zero_178 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8851''45'zero_178 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         (\ v3 ->
            coe
              MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8852'y'8776'x_166
              v0 v1 v3 (coe v2 v3)))
      (coe
         (\ v3 ->
            coe
              MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8852'y'8776'y_160
              v0 v3 v1 (coe v2 v3)))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-zeroʳ
d_'8851''45'zero'691'_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8851''45'zero'691'_180 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_'8851''45'zero'691'_180 v4 v5 v6 v7
du_'8851''45'zero'691'_180 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_'8851''45'zero'691'_180 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8852'y'8776'y_160
      v0 v3 v1 (coe v2 v3)
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-zeroˡ
d_'8851''45'zero'737'_182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8851''45'zero'737'_182 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_'8851''45'zero'737'_182 v4 v5 v6 v7
du_'8851''45'zero'737'_182 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_'8851''45'zero'737'_182 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8852'y'8776'x_166
      v0 v1 v3 (coe v2 v3)
-- Algebra.Construct.NaturalChoice.MaxOp.mono-≤-distrib-⊔
d_mono'45''8804''45'distrib'45''8852'_190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
d_mono'45''8804''45'distrib'45''8852'_190 ~v0 ~v1 ~v2 v3 v4 v5 v6
                                          v7
  = du_mono'45''8804''45'distrib'45''8852'_190 v3 v4 v5 v6 v7
du_mono'45''8804''45'distrib'45''8852'_190 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
du_mono'45''8804''45'distrib'45''8852'_190 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_mono'45''8804''45'distrib'45''8851'_3230
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
      (coe v2) (coe v3) (coe (\ v5 v6 -> coe v4 v6 v5))
