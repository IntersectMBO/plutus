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

module MAlonzo.Code.Algebra.Construct.NaturalChoice.MaxOp where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Algebra.Bundles qualified
import MAlonzo.Code.Algebra.Construct.NaturalChoice.Base qualified
import MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp qualified
import MAlonzo.Code.Algebra.Structures qualified
import MAlonzo.Code.Data.Sum.Base qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Algebra.Construct.NaturalChoice.MaxOp._._≈_
d__'8776'__22 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__22 = erased
-- Algebra.Construct.NaturalChoice.MaxOp._._≲_
d__'8818'__24 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> ()
d__'8818'__24 = erased
-- Algebra.Construct.NaturalChoice.MaxOp.Min.x≤y⇒x⊓z≤y
d_x'8804'y'8658'x'8851'z'8804'y_98 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8658'x'8851'z'8804'y_98 ~v0 ~v1 ~v2 v3 v4
  = du_x'8804'y'8658'x'8851'z'8804'y_98 v3 v4
du_x'8804'y'8658'x'8851'z'8804'y_98 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'y'8658'x'8851'z'8804'y_98 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'x'8851'z'8804'y_3160
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.x≤y⇒z⊓x≤y
d_x'8804'y'8658'z'8851'x'8804'y_100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8658'z'8851'x'8804'y_100 ~v0 ~v1 ~v2 v3 v4
  = du_x'8804'y'8658'z'8851'x'8804'y_100 v3 v4
du_x'8804'y'8658'z'8851'x'8804'y_100 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'y'8658'z'8851'x'8804'y_100 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'z'8851'x'8804'y_3172
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.x≤y⊓z⇒x≤y
d_x'8804'y'8851'z'8658'x'8804'y_102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8851'z'8658'x'8804'y_102 ~v0 ~v1 ~v2 v3 v4
  = du_x'8804'y'8851'z'8658'x'8804'y_102 v3 v4
du_x'8804'y'8851'z'8658'x'8804'y_102 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'y'8851'z'8658'x'8804'y_102 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'y_3184
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.x≤y⊓z⇒x≤z
d_x'8804'y'8851'z'8658'x'8804'z_104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8851'z'8658'x'8804'z_104 ~v0 ~v1 ~v2 v3 v4
  = du_x'8804'y'8851'z'8658'x'8804'z_104 v3 v4
du_x'8804'y'8851'z'8658'x'8804'z_104 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'y'8851'z'8658'x'8804'z_104 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'z_3198
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.x⊓y≈x⇒x≤y
d_x'8851'y'8776'x'8658'x'8804'y_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8851'y'8776'x'8658'x'8804'y_106 ~v0 ~v1 ~v2 v3 v4
  = du_x'8851'y'8776'x'8658'x'8804'y_106 v3 v4
du_x'8851'y'8776'x'8658'x'8804'y_106 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8851'y'8776'x'8658'x'8804'y_106 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'x'8658'x'8804'y_3068
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.x⊓y≈y⇒y≤x
d_x'8851'y'8776'y'8658'y'8804'x_108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8851'y'8776'y'8658'y'8804'x_108 ~v0 ~v1 ~v2 v3 v4
  = du_x'8851'y'8776'y'8658'y'8804'x_108 v3 v4
du_x'8851'y'8776'y'8658'y'8804'x_108 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8851'y'8776'y'8658'y'8804'x_108 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'y'8658'y'8804'x_3100
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.x⊓y≤x
d_x'8851'y'8804'x_110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_x'8851'y'8804'x_110 ~v0 ~v1 ~v2 v3 v4
  = du_x'8851'y'8804'x_110 v3 v4
du_x'8851'y'8804'x_110 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_x'8851'y'8804'x_110 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2808
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.x⊓y≤y
d_x'8851'y'8804'y_112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_x'8851'y'8804'y_112 ~v0 ~v1 ~v2 v3 v4
  = du_x'8851'y'8804'y_112 v3 v4
du_x'8851'y'8804'y_112 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_x'8851'y'8804'y_112 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2834
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-assoc
d_'8851''45'assoc_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'assoc_114 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'assoc_114 v3 v4
du_'8851''45'assoc_114 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'assoc_114 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'assoc_2944
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-band
d_'8851''45'band_116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Bundles.T_Band_596
d_'8851''45'band_116 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'band_116 v3 v4
du_'8851''45'band_116 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Bundles.T_Band_596
du_'8851''45'band_116 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'band_3052
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-comm
d_'8851''45'comm_118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'comm_118 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'comm_118 v3 v4
du_'8851''45'comm_118 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'comm_118 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'comm_2856
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-commutativeSemigroup
d_'8851''45'commutativeSemigroup_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662
d_'8851''45'commutativeSemigroup_120 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'commutativeSemigroup_120 v3 v4
du_'8851''45'commutativeSemigroup_120 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662
du_'8851''45'commutativeSemigroup_120 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'commutativeSemigroup_3054
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-cong
d_'8851''45'cong_122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'cong_122 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'cong_122 v3 v4
du_'8851''45'cong_122 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'cong_122 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong_2930
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-congʳ
d_'8851''45'cong'691'_124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'cong'691'_124 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'cong'691'_124 v3 v4
du_'8851''45'cong'691'_124 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'cong'691'_124 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong'691'_2920
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-congˡ
d_'8851''45'cong'737'_126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'cong'737'_126 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'cong'737'_126 v3 v4
du_'8851''45'cong'737'_126 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'cong'737'_126 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong'737'_2882
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-glb
d_'8851''45'glb_128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'glb_128 ~v0 ~v1 ~v2 v3 v4 = du_'8851''45'glb_128 v3 v4
du_'8851''45'glb_128 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'glb_128 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'glb_3278
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-idem
d_'8851''45'idem_130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny
d_'8851''45'idem_130 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'idem_130 v3 v4
du_'8851''45'idem_130 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny
du_'8851''45'idem_130 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'idem_2984
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-identity
d_'8851''45'identity_132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45'identity_132 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_'8851''45'identity_132 v4 v5 v6
du_'8851''45'identity_132 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8851''45'identity_132 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         (\ v3 ->
            coe
              MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8852'y'8776'y_150
              v0 v1 v3 (coe v2 v3)))
      (coe
         (\ v3 ->
            coe
              MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8852'y'8776'x_156
              v0 v3 v1 (coe v2 v3)))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-identityʳ
d_'8851''45'identity'691'_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8851''45'identity'691'_134 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_'8851''45'identity'691'_134 v4 v5 v6 v7
du_'8851''45'identity'691'_134 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_'8851''45'identity'691'_134 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8852'y'8776'x_156
      v0 v3 v1 (coe v2 v3)
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-identityˡ
d_'8851''45'identity'737'_136 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8851''45'identity'737'_136 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_'8851''45'identity'737'_136 v4 v5 v6 v7
du_'8851''45'identity'737'_136 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_'8851''45'identity'737'_136 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8852'y'8776'y_150
      v0 v1 v3 (coe v2 v3)
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-isBand
d_'8851''45'isBand_138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
d_'8851''45'isBand_138 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'isBand_138 v3 v4
du_'8851''45'isBand_138 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
du_'8851''45'isBand_138 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isBand_3034
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-isCommutativeSemigroup
d_'8851''45'isCommutativeSemigroup_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_548
d_'8851''45'isCommutativeSemigroup_140 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'isCommutativeSemigroup_140 v3 v4
du_'8851''45'isCommutativeSemigroup_140 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_548
du_'8851''45'isCommutativeSemigroup_140 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isCommutativeSemigroup_3036
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-isMagma
d_'8851''45'isMagma_142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'8851''45'isMagma_142 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'isMagma_142 v3 v4
du_'8851''45'isMagma_142 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_'8851''45'isMagma_142 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isMagma_3030
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-isMonoid
d_'8851''45'isMonoid_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_'8851''45'isMonoid_144 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'isMonoid_144 v3 v4
du_'8851''45'isMonoid_144 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
du_'8851''45'isMonoid_144 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isMonoid_3042
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-isSelectiveMagma
d_'8851''45'isSelectiveMagma_146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_436
d_'8851''45'isSelectiveMagma_146 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'isSelectiveMagma_146 v3 v4
du_'8851''45'isSelectiveMagma_146 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_436
du_'8851''45'isSelectiveMagma_146 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3038
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-isSemigroup
d_'8851''45'isSemigroup_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_'8851''45'isSemigroup_148 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'isSemigroup_148 v3 v4
du_'8851''45'isSemigroup_148 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
du_'8851''45'isSemigroup_148 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSemigroup_3032
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-magma
d_'8851''45'magma_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_68
d_'8851''45'magma_150 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'magma_150 v3 v4
du_'8851''45'magma_150 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_68
du_'8851''45'magma_150 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'magma_3048
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-mono-≤
d_'8851''45'mono'45''8804'_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'mono'45''8804'_152 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'mono'45''8804'_152 v3 v4
du_'8851''45'mono'45''8804'_152 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'mono'45''8804'_152 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'45''8804'_3206
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-monoid
d_'8851''45'monoid_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Algebra.Bundles.T_Monoid_882
d_'8851''45'monoid_154 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'monoid_154 v3 v4
du_'8851''45'monoid_154 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Algebra.Bundles.T_Monoid_882
du_'8851''45'monoid_154 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'monoid_3060
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-monoʳ-≤
d_'8851''45'mono'691''45''8804'_156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'mono'691''45''8804'_156 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'mono'691''45''8804'_156 v3 v4
du_'8851''45'mono'691''45''8804'_156 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'mono'691''45''8804'_156 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'691''45''8804'_3266
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-monoˡ-≤
d_'8851''45'mono'737''45''8804'_158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'mono'737''45''8804'_158 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'mono'737''45''8804'_158 v3 v4
du_'8851''45'mono'737''45''8804'_158 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'mono'737''45''8804'_158 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'737''45''8804'_3256
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-sel
d_'8851''45'sel_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8851''45'sel_162 ~v0 ~v1 ~v2 v3 v4 = du_'8851''45'sel_162 v3 v4
du_'8851''45'sel_162 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'8851''45'sel_162 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'sel_2988
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-selectiveMagma
d_'8851''45'selectiveMagma_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Bundles.T_SelectiveMagma_122
d_'8851''45'selectiveMagma_164 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'selectiveMagma_164 v3 v4
du_'8851''45'selectiveMagma_164 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Bundles.T_SelectiveMagma_122
du_'8851''45'selectiveMagma_164 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'selectiveMagma_3056
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-semigroup
d_'8851''45'semigroup_166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
d_'8851''45'semigroup_166 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'semigroup_166 v3 v4
du_'8851''45'semigroup_166 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
du_'8851''45'semigroup_166 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'semigroup_3050
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-triangulate
d_'8851''45'triangulate_168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'triangulate_168 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'triangulate_168 v3 v4
du_'8851''45'triangulate_168 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'triangulate_168 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'triangulate_3292
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-zero
d_'8851''45'zero_170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45'zero_170 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_'8851''45'zero_170 v4 v5 v6
du_'8851''45'zero_170 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8851''45'zero_170 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         (\ v3 ->
            coe
              MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8852'y'8776'x_156
              v0 v1 v3 (coe v2 v3)))
      (coe
         (\ v3 ->
            coe
              MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8852'y'8776'y_150
              v0 v3 v1 (coe v2 v3)))
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-zeroʳ
d_'8851''45'zero'691'_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8851''45'zero'691'_172 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_'8851''45'zero'691'_172 v4 v5 v6 v7
du_'8851''45'zero'691'_172 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_'8851''45'zero'691'_172 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8852'y'8776'y_150
      v0 v3 v1 (coe v2 v3)
-- Algebra.Construct.NaturalChoice.MaxOp.Min.⊓-zeroˡ
d_'8851''45'zero'737'_174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8851''45'zero'737'_174 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_'8851''45'zero'737'_174 v4 v5 v6 v7
du_'8851''45'zero'737'_174 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_'8851''45'zero'737'_174 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8852'y'8776'x_156
      v0 v1 v3 (coe v2 v3)
-- Algebra.Construct.NaturalChoice.MaxOp.mono-≤-distrib-⊔
d_mono'45''8804''45'distrib'45''8852'_182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
d_mono'45''8804''45'distrib'45''8852'_182 ~v0 ~v1 ~v2 v3 v4 v5 v6
                                          v7
  = du_mono'45''8804''45'distrib'45''8852'_182 v3 v4 v5 v6 v7
du_mono'45''8804''45'distrib'45''8852'_182 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
du_mono'45''8804''45'distrib'45''8852'_182 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_mono'45''8804''45'distrib'45''8851'_3114
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
      (coe v2) (coe v3) (coe (\ v5 v6 -> coe v4 v6 v5))
