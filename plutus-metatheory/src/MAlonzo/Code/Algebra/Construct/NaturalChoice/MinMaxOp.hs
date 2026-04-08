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

module MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Bundles
import qualified MAlonzo.Code.Algebra.Bundles.Raw
import qualified MAlonzo.Code.Algebra.Consequences.Setoid
import qualified MAlonzo.Code.Algebra.Construct.NaturalChoice.Base
import qualified MAlonzo.Code.Algebra.Construct.NaturalChoice.MaxOp
import qualified MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Double
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Algebra.Construct.NaturalChoice.MinMaxOp._._≈_
d__'8776'__24 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__24 = erased
-- Algebra.Construct.NaturalChoice.MinMaxOp._._≲_
d__'8818'__28 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> ()
d__'8818'__28 = erased
-- Algebra.Construct.NaturalChoice.MinMaxOp._._⊓_
d__'8851'__98 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'8851'__98 ~v0 v1 ~v2 = du__'8851'__98 v1
du__'8851'__98 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'8851'__98 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
      (coe v0)
-- Algebra.Construct.NaturalChoice.MinMaxOp._._Absorbs_
d__Absorbs__114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d__Absorbs__114 = erased
-- Algebra.Construct.NaturalChoice.MinMaxOp._._DistributesOver_
d__DistributesOver__116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d__DistributesOver__116 = erased
-- Algebra.Construct.NaturalChoice.MinMaxOp._._DistributesOverʳ_
d__DistributesOver'691'__118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d__DistributesOver'691'__118 = erased
-- Algebra.Construct.NaturalChoice.MinMaxOp._._DistributesOverˡ_
d__DistributesOver'737'__120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d__DistributesOver'737'__120 = erased
-- Algebra.Construct.NaturalChoice.MinMaxOp._.Absorptive
d_Absorptive_126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Absorptive_126 = erased
-- Algebra.Construct.NaturalChoice.MinMaxOp._.mono-≤-distrib-⊓
d_mono'45''8804''45'distrib'45''8851'_3070 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
d_mono'45''8804''45'distrib'45''8851'_3070 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_mono'45''8804''45'distrib'45''8851'_3070 v3 v4
du_mono'45''8804''45'distrib'45''8851'_3070 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
du_mono'45''8804''45'distrib'45''8851'_3070 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_mono'45''8804''45'distrib'45''8851'_3230
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.x≤y⇒x⊓z≤y
d_x'8804'y'8658'x'8851'z'8804'y_3072 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8658'x'8851'z'8804'y_3072 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_x'8804'y'8658'x'8851'z'8804'y_3072 v3 v4
du_x'8804'y'8658'x'8851'z'8804'y_3072 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'y'8658'x'8851'z'8804'y_3072 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'x'8851'z'8804'y_3276
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.x≤y⇒z⊓x≤y
d_x'8804'y'8658'z'8851'x'8804'y_3074 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8658'z'8851'x'8804'y_3074 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_x'8804'y'8658'z'8851'x'8804'y_3074 v3 v4
du_x'8804'y'8658'z'8851'x'8804'y_3074 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'y'8658'z'8851'x'8804'y_3074 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'z'8851'x'8804'y_3288
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.x≤y⊓z⇒x≤y
d_x'8804'y'8851'z'8658'x'8804'y_3076 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8851'z'8658'x'8804'y_3076 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_x'8804'y'8851'z'8658'x'8804'y_3076 v3 v4
du_x'8804'y'8851'z'8658'x'8804'y_3076 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'y'8851'z'8658'x'8804'y_3076 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'y_3300
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.x≤y⊓z⇒x≤z
d_x'8804'y'8851'z'8658'x'8804'z_3078 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8851'z'8658'x'8804'z_3078 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_x'8804'y'8851'z'8658'x'8804'z_3078 v3 v4
du_x'8804'y'8851'z'8658'x'8804'z_3078 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'y'8851'z'8658'x'8804'z_3078 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'z_3314
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.x⊓y≈x⇒x≤y
d_x'8851'y'8776'x'8658'x'8804'y_3080 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8851'y'8776'x'8658'x'8804'y_3080 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_x'8851'y'8776'x'8658'x'8804'y_3080 v3 v4
du_x'8851'y'8776'x'8658'x'8804'y_3080 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8851'y'8776'x'8658'x'8804'y_3080 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'x'8658'x'8804'y_3184
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.x⊓y≈y⇒y≤x
d_x'8851'y'8776'y'8658'y'8804'x_3082 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8851'y'8776'y'8658'y'8804'x_3082 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_x'8851'y'8776'y'8658'y'8804'x_3082 v3 v4
du_x'8851'y'8776'y'8658'y'8804'x_3082 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8851'y'8776'y'8658'y'8804'x_3082 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'y'8658'y'8804'x_3216
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.x⊓y≤x
d_x'8851'y'8804'x_3084 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_x'8851'y'8804'x_3084 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_x'8851'y'8804'x_3084 v3 v4
du_x'8851'y'8804'x_3084 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_x'8851'y'8804'x_3084 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2924
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.x⊓y≤y
d_x'8851'y'8804'y_3086 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_x'8851'y'8804'y_3086 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_x'8851'y'8804'y_3086 v3 v4
du_x'8851'y'8804'y_3086 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_x'8851'y'8804'y_3086 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2950
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-assoc
d_'8851''45'assoc_3088 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'assoc_3088 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'assoc_3088 v3 v4
du_'8851''45'assoc_3088 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'assoc_3088 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'assoc_3060
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-band
d_'8851''45'band_3090 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Bundles.T_Band_620
d_'8851''45'band_3090 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'band_3090 v3 v4
du_'8851''45'band_3090 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Bundles.T_Band_620
du_'8851''45'band_3090 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'band_3168
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-comm
d_'8851''45'comm_3092 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'comm_3092 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'comm_3092 v3 v4
du_'8851''45'comm_3092 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'comm_3092 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'comm_2972
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-commutativeSemigroup
d_'8851''45'commutativeSemigroup_3094 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_688
d_'8851''45'commutativeSemigroup_3094 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'commutativeSemigroup_3094 v3 v4
du_'8851''45'commutativeSemigroup_3094 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_688
du_'8851''45'commutativeSemigroup_3094 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'commutativeSemigroup_3170
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-cong
d_'8851''45'cong_3096 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'cong_3096 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'cong_3096 v3 v4
du_'8851''45'cong_3096 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'cong_3096 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong_3046
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-congʳ
d_'8851''45'cong'691'_3098 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'cong'691'_3098 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'cong'691'_3098 v3 v4
du_'8851''45'cong'691'_3098 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'cong'691'_3098 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong'691'_3036
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-congˡ
d_'8851''45'cong'737'_3100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'cong'737'_3100 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'cong'737'_3100 v3 v4
du_'8851''45'cong'737'_3100 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'cong'737'_3100 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong'737'_2998
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-glb
d_'8851''45'glb_3102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'glb_3102 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'glb_3102 v3 v4
du_'8851''45'glb_3102 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'glb_3102 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'glb_3394
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-idem
d_'8851''45'idem_3104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny
d_'8851''45'idem_3104 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'idem_3104 v3 v4
du_'8851''45'idem_3104 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny
du_'8851''45'idem_3104 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'idem_3100
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-identity
d_'8851''45'identity_3106 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45'identity_3106 ~v0 v1 ~v2 v3 v4
  = du_'8851''45'identity_3106 v1 v3 v4
du_'8851''45'identity_3106 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8851''45'identity_3106 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         (\ v3 ->
            coe
              MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8851'y'8776'y_134
              v0 v1 v3 (coe v2 v3)))
      (coe
         (\ v3 ->
            coe
              MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_128
              v0 v3 v1 (coe v2 v3)))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-identityʳ
d_'8851''45'identity'691'_3108 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8851''45'identity'691'_3108 ~v0 v1 ~v2 v3 v4 v5
  = du_'8851''45'identity'691'_3108 v1 v3 v4 v5
du_'8851''45'identity'691'_3108 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_'8851''45'identity'691'_3108 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_128
      v0 v3 v1 (coe v2 v3)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-identityˡ
d_'8851''45'identity'737'_3110 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8851''45'identity'737'_3110 ~v0 v1 ~v2 v3 v4 v5
  = du_'8851''45'identity'737'_3110 v1 v3 v4 v5
du_'8851''45'identity'737'_3110 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_'8851''45'identity'737'_3110 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8851'y'8776'y_134
      v0 v1 v3 (coe v2 v3)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-isBand
d_'8851''45'isBand_3112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_'8851''45'isBand_3112 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'isBand_3112 v3 v4
du_'8851''45'isBand_3112 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
du_'8851''45'isBand_3112 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isBand_3150
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-isCommutativeSemigroup
d_'8851''45'isCommutativeSemigroup_3114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_'8851''45'isCommutativeSemigroup_3114 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'isCommutativeSemigroup_3114 v3 v4
du_'8851''45'isCommutativeSemigroup_3114 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_'8851''45'isCommutativeSemigroup_3114 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isCommutativeSemigroup_3152
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-isMagma
d_'8851''45'isMagma_3116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'8851''45'isMagma_3116 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'isMagma_3116 v3 v4
du_'8851''45'isMagma_3116 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_'8851''45'isMagma_3116 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isMagma_3146
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-isMonoid
d_'8851''45'isMonoid_3118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'8851''45'isMonoid_3118 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'isMonoid_3118 v3 v4
du_'8851''45'isMonoid_3118 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
du_'8851''45'isMonoid_3118 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isMonoid_3158
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-isSelectiveMagma
d_'8851''45'isSelectiveMagma_3120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450
d_'8851''45'isSelectiveMagma_3120 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'isSelectiveMagma_3120 v3 v4
du_'8851''45'isSelectiveMagma_3120 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450
du_'8851''45'isSelectiveMagma_3120 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3154
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-isSemigroup
d_'8851''45'isSemigroup_3122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'8851''45'isSemigroup_3122 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'isSemigroup_3122 v3 v4
du_'8851''45'isSemigroup_3122 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_'8851''45'isSemigroup_3122 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSemigroup_3148
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-magma
d_'8851''45'magma_3124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_74
d_'8851''45'magma_3124 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'magma_3124 v3 v4
du_'8851''45'magma_3124 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_74
du_'8851''45'magma_3124 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'magma_3164
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-mono-≤
d_'8851''45'mono'45''8804'_3126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'mono'45''8804'_3126 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'mono'45''8804'_3126 v3 v4
du_'8851''45'mono'45''8804'_3126 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'mono'45''8804'_3126 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'45''8804'_3322
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-monoid
d_'8851''45'monoid_3128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Algebra.Bundles.T_Monoid_914
d_'8851''45'monoid_3128 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'monoid_3128 v3 v4
du_'8851''45'monoid_3128 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Algebra.Bundles.T_Monoid_914
du_'8851''45'monoid_3128 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'monoid_3176
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-monoʳ-≤
d_'8851''45'mono'691''45''8804'_3130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'mono'691''45''8804'_3130 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'mono'691''45''8804'_3130 v3 v4
du_'8851''45'mono'691''45''8804'_3130 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'mono'691''45''8804'_3130 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'691''45''8804'_3382
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-monoˡ-≤
d_'8851''45'mono'737''45''8804'_3132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'mono'737''45''8804'_3132 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'mono'737''45''8804'_3132 v3 v4
du_'8851''45'mono'737''45''8804'_3132 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'mono'737''45''8804'_3132 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'737''45''8804'_3372
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-rawMagma
d_'8851''45'rawMagma_3134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44
d_'8851''45'rawMagma_3134 ~v0 ~v1 ~v2 ~v3 v4 ~v5
  = du_'8851''45'rawMagma_3134 v4
du_'8851''45'rawMagma_3134 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44
du_'8851''45'rawMagma_3134 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'rawMagma_3162
      (coe v0)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-sel
d_'8851''45'sel_3136 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8851''45'sel_3136 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'sel_3136 v3 v4
du_'8851''45'sel_3136 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'8851''45'sel_3136 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'sel_3104
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-selectiveMagma
d_'8851''45'selectiveMagma_3138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Bundles.T_SelectiveMagma_130
d_'8851''45'selectiveMagma_3138 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'selectiveMagma_3138 v3 v4
du_'8851''45'selectiveMagma_3138 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Bundles.T_SelectiveMagma_130
du_'8851''45'selectiveMagma_3138 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'selectiveMagma_3172
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-semigroup
d_'8851''45'semigroup_3140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
d_'8851''45'semigroup_3140 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'semigroup_3140 v3 v4
du_'8851''45'semigroup_3140 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
du_'8851''45'semigroup_3140 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'semigroup_3166
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-triangulate
d_'8851''45'triangulate_3142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'triangulate_3142 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'triangulate_3142 v3 v4
du_'8851''45'triangulate_3142 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'triangulate_3142 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'triangulate_3408
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-zero
d_'8851''45'zero_3144 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45'zero_3144 ~v0 v1 ~v2 v3 v4
  = du_'8851''45'zero_3144 v1 v3 v4
du_'8851''45'zero_3144 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8851''45'zero_3144 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         (\ v3 ->
            coe
              MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_128
              v0 v1 v3 (coe v2 v3)))
      (coe
         (\ v3 ->
            coe
              MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8851'y'8776'y_134
              v0 v3 v1 (coe v2 v3)))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-zeroʳ
d_'8851''45'zero'691'_3146 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8851''45'zero'691'_3146 ~v0 v1 ~v2 v3 v4 v5
  = du_'8851''45'zero'691'_3146 v1 v3 v4 v5
du_'8851''45'zero'691'_3146 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_'8851''45'zero'691'_3146 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8851'y'8776'y_134
      v0 v3 v1 (coe v2 v3)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-zeroˡ
d_'8851''45'zero'737'_3148 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8851''45'zero'737'_3148 ~v0 v1 ~v2 v3 v4 v5
  = du_'8851''45'zero'737'_3148 v1 v3 v4 v5
du_'8851''45'zero'737'_3148 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_'8851''45'zero'737'_3148 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_128
      v0 v1 v3 (coe v2 v3)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.mono-≤-distrib-⊔
d_mono'45''8804''45'distrib'45''8852'_3152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
d_mono'45''8804''45'distrib'45''8852'_3152 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_mono'45''8804''45'distrib'45''8852'_3152 v3 v5
du_mono'45''8804''45'distrib'45''8852'_3152 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
du_mono'45''8804''45'distrib'45''8852'_3152 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MaxOp.du_mono'45''8804''45'distrib'45''8852'_190
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.x⊓y≤x
d_x'8851'y'8804'x_3154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_x'8851'y'8804'x_3154 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_x'8851'y'8804'x_3154 v3 v5
du_x'8851'y'8804'x_3154 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_x'8851'y'8804'x_3154 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2924
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.x≤y⇒x⊓z≤y
d_x'8804'y'8658'x'8851'z'8804'y_3156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8658'x'8851'z'8804'y_3156 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_x'8804'y'8658'x'8851'z'8804'y_3156 v3 v5
du_x'8804'y'8658'x'8851'z'8804'y_3156 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'y'8658'x'8851'z'8804'y_3156 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'x'8851'z'8804'y_3276
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.x≤y⇒z⊓x≤y
d_x'8804'y'8658'z'8851'x'8804'y_3158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8658'z'8851'x'8804'y_3158 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_x'8804'y'8658'z'8851'x'8804'y_3158 v3 v5
du_x'8804'y'8658'z'8851'x'8804'y_3158 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'y'8658'z'8851'x'8804'y_3158 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'z'8851'x'8804'y_3288
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.x⊓y≤y
d_x'8851'y'8804'y_3160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_x'8851'y'8804'y_3160 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_x'8851'y'8804'y_3160 v3 v5
du_x'8851'y'8804'y_3160 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_x'8851'y'8804'y_3160 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2950
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.x⊓y≈x⇒x≤y
d_x'8851'y'8776'x'8658'x'8804'y_3162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8851'y'8776'x'8658'x'8804'y_3162 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_x'8851'y'8776'x'8658'x'8804'y_3162 v3 v5
du_x'8851'y'8776'x'8658'x'8804'y_3162 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8851'y'8776'x'8658'x'8804'y_3162 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'x'8658'x'8804'y_3184
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.x⊓y≈y⇒y≤x
d_x'8851'y'8776'y'8658'y'8804'x_3164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8851'y'8776'y'8658'y'8804'x_3164 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_x'8851'y'8776'y'8658'y'8804'x_3164 v3 v5
du_x'8851'y'8776'y'8658'y'8804'x_3164 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8851'y'8776'y'8658'y'8804'x_3164 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'y'8658'y'8804'x_3216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.x≤y⊓z⇒x≤y
d_x'8804'y'8851'z'8658'x'8804'y_3166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8851'z'8658'x'8804'y_3166 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_x'8804'y'8851'z'8658'x'8804'y_3166 v3 v5
du_x'8804'y'8851'z'8658'x'8804'y_3166 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'y'8851'z'8658'x'8804'y_3166 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'y_3300
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.x≤y⊓z⇒x≤z
d_x'8804'y'8851'z'8658'x'8804'z_3168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8851'z'8658'x'8804'z_3168 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_x'8804'y'8851'z'8658'x'8804'z_3168 v3 v5
du_x'8804'y'8851'z'8658'x'8804'z_3168 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'y'8851'z'8658'x'8804'z_3168 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'z_3314
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-assoc
d_'8851''45'assoc_3170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'assoc_3170 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'assoc_3170 v3 v5
du_'8851''45'assoc_3170 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'assoc_3170 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'assoc_3060
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-band
d_'8851''45'band_3172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Bundles.T_Band_620
d_'8851''45'band_3172 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'band_3172 v3 v5
du_'8851''45'band_3172 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Bundles.T_Band_620
du_'8851''45'band_3172 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'band_3168
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-comm
d_'8851''45'comm_3174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'comm_3174 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'comm_3174 v3 v5
du_'8851''45'comm_3174 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'comm_3174 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'comm_2972
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-commutativeSemigroup
d_'8851''45'commutativeSemigroup_3176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_688
d_'8851''45'commutativeSemigroup_3176 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'commutativeSemigroup_3176 v3 v5
du_'8851''45'commutativeSemigroup_3176 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_688
du_'8851''45'commutativeSemigroup_3176 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'commutativeSemigroup_3170
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-cong
d_'8851''45'cong_3178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'cong_3178 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'cong_3178 v3 v5
du_'8851''45'cong_3178 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'cong_3178 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong_3046
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-congʳ
d_'8851''45'cong'691'_3180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'cong'691'_3180 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'cong'691'_3180 v3 v5
du_'8851''45'cong'691'_3180 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'cong'691'_3180 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong'691'_3036
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-congˡ
d_'8851''45'cong'737'_3182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'cong'737'_3182 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'cong'737'_3182 v3 v5
du_'8851''45'cong'737'_3182 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'cong'737'_3182 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong'737'_2998
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-idem
d_'8851''45'idem_3184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny
d_'8851''45'idem_3184 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'idem_3184 v3 v5
du_'8851''45'idem_3184 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny
du_'8851''45'idem_3184 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'idem_3100
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-identity
d_'8851''45'identity_3186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45'identity_3186 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_'8851''45'identity_3186 v5 v6 v7
du_'8851''45'identity_3186 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8851''45'identity_3186 v0 v1 v2
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
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-identityʳ
d_'8851''45'identity'691'_3188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8851''45'identity'691'_3188 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8
  = du_'8851''45'identity'691'_3188 v5 v6 v7 v8
du_'8851''45'identity'691'_3188 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_'8851''45'identity'691'_3188 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8852'y'8776'x_166
      v0 v3 v1 (coe v2 v3)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-identityˡ
d_'8851''45'identity'737'_3190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8851''45'identity'737'_3190 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8
  = du_'8851''45'identity'737'_3190 v5 v6 v7 v8
du_'8851''45'identity'737'_3190 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_'8851''45'identity'737'_3190 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8852'y'8776'y_160
      v0 v1 v3 (coe v2 v3)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-isBand
d_'8851''45'isBand_3192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_'8851''45'isBand_3192 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'isBand_3192 v3 v5
du_'8851''45'isBand_3192 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
du_'8851''45'isBand_3192 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isBand_3150
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-isCommutativeSemigroup
d_'8851''45'isCommutativeSemigroup_3194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_'8851''45'isCommutativeSemigroup_3194 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'isCommutativeSemigroup_3194 v3 v5
du_'8851''45'isCommutativeSemigroup_3194 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_'8851''45'isCommutativeSemigroup_3194 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isCommutativeSemigroup_3152
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-isMagma
d_'8851''45'isMagma_3196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'8851''45'isMagma_3196 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'isMagma_3196 v3 v5
du_'8851''45'isMagma_3196 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_'8851''45'isMagma_3196 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isMagma_3146
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-isMonoid
d_'8851''45'isMonoid_3198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'8851''45'isMonoid_3198 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'isMonoid_3198 v3 v5
du_'8851''45'isMonoid_3198 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
du_'8851''45'isMonoid_3198 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isMonoid_3158
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-isSelectiveMagma
d_'8851''45'isSelectiveMagma_3200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450
d_'8851''45'isSelectiveMagma_3200 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'isSelectiveMagma_3200 v3 v5
du_'8851''45'isSelectiveMagma_3200 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450
du_'8851''45'isSelectiveMagma_3200 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3154
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-isSemigroup
d_'8851''45'isSemigroup_3202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'8851''45'isSemigroup_3202 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'isSemigroup_3202 v3 v5
du_'8851''45'isSemigroup_3202 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_'8851''45'isSemigroup_3202 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSemigroup_3148
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-glb
d_'8851''45'glb_3204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'glb_3204 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'glb_3204 v3 v5
du_'8851''45'glb_3204 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'glb_3204 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'glb_3394
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-magma
d_'8851''45'magma_3206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_74
d_'8851''45'magma_3206 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'magma_3206 v3 v5
du_'8851''45'magma_3206 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_74
du_'8851''45'magma_3206 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'magma_3164
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-mono-≤
d_'8851''45'mono'45''8804'_3208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'mono'45''8804'_3208 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'mono'45''8804'_3208 v3 v5
du_'8851''45'mono'45''8804'_3208 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'mono'45''8804'_3208 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'45''8804'_3322
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-monoid
d_'8851''45'monoid_3210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Algebra.Bundles.T_Monoid_914
d_'8851''45'monoid_3210 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'monoid_3210 v3 v5
du_'8851''45'monoid_3210 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Algebra.Bundles.T_Monoid_914
du_'8851''45'monoid_3210 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'monoid_3176
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-monoʳ-≤
d_'8851''45'mono'691''45''8804'_3212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'mono'691''45''8804'_3212 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'mono'691''45''8804'_3212 v3 v5
du_'8851''45'mono'691''45''8804'_3212 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'mono'691''45''8804'_3212 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'691''45''8804'_3382
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-monoˡ-≤
d_'8851''45'mono'737''45''8804'_3214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'mono'737''45''8804'_3214 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'mono'737''45''8804'_3214 v3 v5
du_'8851''45'mono'737''45''8804'_3214 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'mono'737''45''8804'_3214 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'737''45''8804'_3372
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-sel
d_'8851''45'sel_3216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8851''45'sel_3216 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'sel_3216 v3 v5
du_'8851''45'sel_3216 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'8851''45'sel_3216 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'sel_3104
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-selectiveMagma
d_'8851''45'selectiveMagma_3218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Bundles.T_SelectiveMagma_130
d_'8851''45'selectiveMagma_3218 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'selectiveMagma_3218 v3 v5
du_'8851''45'selectiveMagma_3218 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Bundles.T_SelectiveMagma_130
du_'8851''45'selectiveMagma_3218 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'selectiveMagma_3172
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-semigroup
d_'8851''45'semigroup_3220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
d_'8851''45'semigroup_3220 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'semigroup_3220 v3 v5
du_'8851''45'semigroup_3220 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
du_'8851''45'semigroup_3220 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'semigroup_3166
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-triangulate
d_'8851''45'triangulate_3222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'triangulate_3222 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'triangulate_3222 v3 v5
du_'8851''45'triangulate_3222 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'triangulate_3222 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'triangulate_3408
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-zero
d_'8851''45'zero_3224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45'zero_3224 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_'8851''45'zero_3224 v5 v6 v7
du_'8851''45'zero_3224 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8851''45'zero_3224 v0 v1 v2
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
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-zeroʳ
d_'8851''45'zero'691'_3226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8851''45'zero'691'_3226 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8
  = du_'8851''45'zero'691'_3226 v5 v6 v7 v8
du_'8851''45'zero'691'_3226 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_'8851''45'zero'691'_3226 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8852'y'8776'y_160
      v0 v3 v1 (coe v2 v3)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-zeroˡ
d_'8851''45'zero'737'_3228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8851''45'zero'737'_3228 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8
  = du_'8851''45'zero'737'_3228 v5 v6 v7 v8
du_'8851''45'zero'737'_3228 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_'8851''45'zero'737'_3228 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8852'y'8776'x_166
      v0 v1 v3 (coe v2 v3)
-- Algebra.Construct.NaturalChoice.MinMaxOp.⊓-distribˡ-⊔
d_'8851''45'distrib'737''45''8852'_3230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'distrib'737''45''8852'_3230 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7
                                        v8
  = du_'8851''45'distrib'737''45''8852'_3230 v3 v4 v5 v6 v7 v8
du_'8851''45'distrib'737''45''8852'_3230 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'distrib'737''45''8852'_3230 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Relation.Binary.Structures.d_total_142
              (MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                 (coe v0))
              v4 v5 in
    coe
      (case coe v6 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
           -> coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_equalitySubRelation_152)
                (coe
                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                   v3
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                      v4 v5))
                (coe
                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      v3 v4)
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      v3 v5))
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                      (coe
                         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                         (coe
                            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                            (coe v0))))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      v3
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                         v4 v5))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      v3 v5)
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         v3 v4)
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         v3 v5))
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                         (coe
                            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                            (coe
                               MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                               (coe v0))))
                      (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                         (coe
                            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                            (coe
                               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                               (coe
                                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                  (coe v0)))))
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         v3 v5)
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                            v3 v4)
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                            v3 v5))
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                            v3 v4)
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                            v3 v5))
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                            (coe
                               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                               (coe
                                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                  (coe v0))))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                               v3 v4)
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                               v3 v5)))
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8852'y'8776'y_160
                         v2
                         (coe
                            MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                               v3)
                            (\ v8 v9 -> v8) v4 v5)
                         (coe
                            MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                            (\ v8 v9 -> v9)
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                               v3)
                            v4 v5)
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'691''45''8804'_3382
                            (coe v0) (coe v1) (coe v3) (coe v4) (coe v5) (coe v7))))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong'737'_2998
                      (coe v0) (coe v1) (coe v3)
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                         v4 v5)
                      (coe v5)
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8852'y'8776'y_160
                         v2 v4 v5 v7)))
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
           -> coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_equalitySubRelation_152)
                (coe
                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                   v3
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                      v4 v5))
                (coe
                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      v3 v4)
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      v3 v5))
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                      (coe
                         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                         (coe
                            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                            (coe v0))))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      v3
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                         v4 v5))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      v3 v4)
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         v3 v4)
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         v3 v5))
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                         (coe
                            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                            (coe
                               MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                               (coe v0))))
                      (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                         (coe
                            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                            (coe
                               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                               (coe
                                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                  (coe v0)))))
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         v3 v4)
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                            v3 v4)
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                            v3 v5))
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                            v3 v4)
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                            v3 v5))
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                            (coe
                               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                               (coe
                                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                  (coe v0))))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                               v3 v4)
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                               v3 v5)))
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8852'y'8776'x_166
                         v2
                         (coe
                            MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                            (\ v8 v9 -> v9)
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                               v3)
                            v5 v4)
                         (coe
                            MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                               v3)
                            (\ v8 v9 -> v8) v5 v4)
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'691''45''8804'_3382
                            (coe v0) (coe v1) (coe v3) (coe v5) (coe v4) (coe v7))))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong'737'_2998
                      (coe v0) (coe v1) (coe v3)
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                         v4 v5)
                      (coe v4)
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8852'y'8776'x_166
                         v2 v4 v5 v7)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Algebra.Construct.NaturalChoice.MinMaxOp.⊓-distribʳ-⊔
d_'8851''45'distrib'691''45''8852'_3258 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'distrib'691''45''8852'_3258 ~v0 ~v1 ~v2 v3 v4 v5
  = du_'8851''45'distrib'691''45''8852'_3258 v3 v4 v5
du_'8851''45'distrib'691''45''8852'_3258 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'distrib'691''45''8852'_3258 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Consequences.Setoid.du_comm'8743'distr'737''8658'distr'691'_536
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_setoid_190
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_preorder_270 (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
         (coe v1))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154
         (coe v2))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong_3046
         (coe
            MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
            (coe v0))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
            (coe v2)))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'comm_2972
         (coe v0) (coe v1))
      (coe
         du_'8851''45'distrib'737''45''8852'_3230 (coe v0) (coe v1)
         (coe v2))
-- Algebra.Construct.NaturalChoice.MinMaxOp.⊓-distrib-⊔
d_'8851''45'distrib'45''8852'_3260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45'distrib'45''8852'_3260 ~v0 ~v1 ~v2 v3 v4 v5
  = du_'8851''45'distrib'45''8852'_3260 v3 v4 v5
du_'8851''45'distrib'45''8852'_3260 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8851''45'distrib'45''8852'_3260 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         du_'8851''45'distrib'737''45''8852'_3230 (coe v0) (coe v1)
         (coe v2))
      (coe
         du_'8851''45'distrib'691''45''8852'_3258 (coe v0) (coe v1)
         (coe v2))
-- Algebra.Construct.NaturalChoice.MinMaxOp.⊔-distribˡ-⊓
d_'8852''45'distrib'737''45''8851'_3262 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8852''45'distrib'737''45''8851'_3262 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7
                                        v8
  = du_'8852''45'distrib'737''45''8851'_3262 v3 v4 v5 v6 v7 v8
du_'8852''45'distrib'737''45''8851'_3262 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8852''45'distrib'737''45''8851'_3262 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Relation.Binary.Structures.d_total_142
              (MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                 (coe v0))
              v4 v5 in
    coe
      (case coe v6 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
           -> coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_equalitySubRelation_152)
                (coe
                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                   v3
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      v4 v5))
                (coe
                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                      v3 v4)
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                      v3 v5))
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                      (coe
                         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                         (coe
                            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                            (coe v0))))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                      v3
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         v4 v5))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                      v3 v4)
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                         v3 v4)
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                         v3 v5))
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                         (coe
                            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                            (coe
                               MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                               (coe v0))))
                      (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                         (coe
                            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                            (coe
                               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                               (coe
                                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                  (coe v0)))))
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                         v3 v4)
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                            v3 v4)
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                            v3 v5))
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                            v3 v4)
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                            v3 v5))
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                            (coe
                               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                               (coe
                                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                  (coe v0))))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                               v3 v4)
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                               v3 v5)))
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_128
                         v1
                         (coe
                            MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                            (\ v8 v9 -> v9)
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                               v3)
                            v5 v4)
                         (coe
                            MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                               v3)
                            (\ v8 v9 -> v8) v5 v4)
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'691''45''8804'_3382
                            (coe
                               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
                               (coe v0))
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
                               (coe v2))
                            (coe v3) (coe v5) (coe v4) (coe v7))))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong'737'_2998
                      (coe
                         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
                         (coe v0))
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
                         (coe v2))
                      (coe v3)
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         v4 v5)
                      (coe v4)
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_128
                         v1 v4 v5 v7)))
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
           -> coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_equalitySubRelation_152)
                (coe
                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                   v3
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      v4 v5))
                (coe
                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                      v3 v4)
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                      v3 v5))
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                      (coe
                         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                         (coe
                            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                            (coe v0))))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                      v3
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         v4 v5))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                      v3 v5)
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                         v3 v4)
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                         v3 v5))
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                         (coe
                            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                            (coe
                               MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                               (coe v0))))
                      (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                         (coe
                            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                            (coe
                               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                               (coe
                                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                  (coe v0)))))
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                         v3 v5)
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                            v3 v4)
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                            v3 v5))
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                            v3 v4)
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                            v3 v5))
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                            (coe
                               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                               (coe
                                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                  (coe v0))))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                               v3 v4)
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                               v3 v5)))
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8851'y'8776'y_134
                         v1
                         (coe
                            MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                               v3)
                            (\ v8 v9 -> v8) v4 v5)
                         (coe
                            MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                            (\ v8 v9 -> v9)
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                               v3)
                            v4 v5)
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'691''45''8804'_3382
                            (coe
                               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
                               (coe v0))
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
                               (coe v2))
                            (coe v3) (coe v4) (coe v5) (coe v7))))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong'737'_2998
                      (coe
                         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
                         (coe v0))
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
                         (coe v2))
                      (coe v3)
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         v4 v5)
                      (coe v5)
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8851'y'8776'y_134
                         v1 v4 v5 v7)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Algebra.Construct.NaturalChoice.MinMaxOp.⊔-distribʳ-⊓
d_'8852''45'distrib'691''45''8851'_3290 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8852''45'distrib'691''45''8851'_3290 ~v0 ~v1 ~v2 v3 v4 v5
  = du_'8852''45'distrib'691''45''8851'_3290 v3 v4 v5
du_'8852''45'distrib'691''45''8851'_3290 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8852''45'distrib'691''45''8851'_3290 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Consequences.Setoid.du_comm'8743'distr'737''8658'distr'691'_536
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_setoid_190
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_preorder_270 (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154
         (coe v2))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
         (coe v1))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong_3046
         (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'comm_2972
         (coe
            MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
            (coe v0))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
            (coe v2)))
      (coe
         du_'8852''45'distrib'737''45''8851'_3262 (coe v0) (coe v1)
         (coe v2))
-- Algebra.Construct.NaturalChoice.MinMaxOp.⊔-distrib-⊓
d_'8852''45'distrib'45''8851'_3292 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8852''45'distrib'45''8851'_3292 ~v0 ~v1 ~v2 v3 v4 v5
  = du_'8852''45'distrib'45''8851'_3292 v3 v4 v5
du_'8852''45'distrib'45''8851'_3292 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8852''45'distrib'45''8851'_3292 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         du_'8852''45'distrib'737''45''8851'_3262 (coe v0) (coe v1)
         (coe v2))
      (coe
         du_'8852''45'distrib'691''45''8851'_3290 (coe v0) (coe v1)
         (coe v2))
-- Algebra.Construct.NaturalChoice.MinMaxOp.⊓-absorbs-⊔
d_'8851''45'absorbs'45''8852'_3294 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'absorbs'45''8852'_3294 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7
  = du_'8851''45'absorbs'45''8852'_3294 v3 v4 v5 v6 v7
du_'8851''45'absorbs'45''8852'_3294 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'absorbs'45''8852'_3294 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Relation.Binary.Structures.d_total_142
              (MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                 (coe v0))
              v3 v4 in
    coe
      (case coe v5 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
           -> coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_equalitySubRelation_152)
                (coe
                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                   v3
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                      v3 v4))
                (coe v3)
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                      (coe
                         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                         (coe
                            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                            (coe v0))))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      v3
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                         v3 v4))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      v3 v4)
                   v3
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                         (coe
                            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                            (coe
                               MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                               (coe v0))))
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         v3 v4)
                      v3 v3
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                            (coe
                               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                               (coe
                                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                  (coe v0))))
                         (coe v3))
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_128
                         v1 v3 v4 v6))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong'737'_2998
                      (coe v0) (coe v1) (coe v3)
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                         v3 v4)
                      (coe v4)
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8852'y'8776'y_160
                         v2 v3 v4 v6)))
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
           -> coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_equalitySubRelation_152)
                (coe
                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                   v3
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                      v3 v4))
                (coe v3)
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                      (coe
                         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                         (coe
                            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                            (coe v0))))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      v3
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                         v3 v4))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      v3 v3)
                   v3
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                         (coe
                            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                            (coe
                               MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                               (coe v0))))
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         v3 v3)
                      v3 v3
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                            (coe
                               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                               (coe
                                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                  (coe v0))))
                         (coe v3))
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'idem_3100
                         (coe v0) (coe v1) (coe v3)))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong'737'_2998
                      (coe v0) (coe v1) (coe v3)
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                         v3 v4)
                      (coe v3)
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8852'y'8776'x_166
                         v2 v3 v4 v6)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Algebra.Construct.NaturalChoice.MinMaxOp.⊔-absorbs-⊓
d_'8852''45'absorbs'45''8851'_3316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8852''45'absorbs'45''8851'_3316 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7
  = du_'8852''45'absorbs'45''8851'_3316 v3 v4 v5 v6 v7
du_'8852''45'absorbs'45''8851'_3316 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8852''45'absorbs'45''8851'_3316 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Relation.Binary.Structures.d_total_142
              (MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                 (coe v0))
              v3 v4 in
    coe
      (case coe v5 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
           -> coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_equalitySubRelation_152)
                (coe
                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                   v3
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      v3 v4))
                (coe v3)
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                      (coe
                         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                         (coe
                            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                            (coe v0))))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                      v3
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         v3 v4))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                      v3 v3)
                   v3
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                         (coe
                            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                            (coe
                               MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                               (coe v0))))
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                         v3 v3)
                      v3 v3
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                            (coe
                               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                               (coe
                                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                  (coe v0))))
                         (coe v3))
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'idem_3100
                         (coe
                            MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
                            (coe v0))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
                            (coe v2))
                         (coe v3)))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong'737'_2998
                      (coe
                         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
                         (coe v0))
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
                         (coe v2))
                      (coe v3)
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         v3 v4)
                      (coe v3)
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_128
                         v1 v3 v4 v6)))
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
           -> coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_equalitySubRelation_152)
                (coe
                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                   v3
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      v3 v4))
                (coe v3)
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                      (coe
                         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                         (coe
                            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                            (coe v0))))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                      v3
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         v3 v4))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                      v3 v4)
                   v3
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                         (coe
                            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                            (coe
                               MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                               (coe v0))))
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                         v3 v4)
                      v3 v3
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                            (coe
                               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                               (coe
                                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                  (coe v0))))
                         (coe v3))
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8852'y'8776'x_166
                         v2 v3 v4 v6))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong'737'_2998
                      (coe
                         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
                         (coe v0))
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
                         (coe v2))
                      (coe v3)
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         v3 v4)
                      (coe v4)
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8851'y'8776'y_134
                         v1 v3 v4 v6)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Algebra.Construct.NaturalChoice.MinMaxOp.⊔-⊓-absorptive
d_'8852''45''8851''45'absorptive_3338 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8852''45''8851''45'absorptive_3338 ~v0 ~v1 ~v2 v3 v4 v5
  = du_'8852''45''8851''45'absorptive_3338 v3 v4 v5
du_'8852''45''8851''45'absorptive_3338 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8852''45''8851''45'absorptive_3338 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         du_'8852''45'absorbs'45''8851'_3316 (coe v0) (coe v1) (coe v2))
      (coe
         du_'8851''45'absorbs'45''8852'_3294 (coe v0) (coe v1) (coe v2))
-- Algebra.Construct.NaturalChoice.MinMaxOp.⊓-⊔-absorptive
d_'8851''45''8852''45'absorptive_3340 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45''8852''45'absorptive_3340 ~v0 ~v1 ~v2 v3 v4 v5
  = du_'8851''45''8852''45'absorptive_3340 v3 v4 v5
du_'8851''45''8852''45'absorptive_3340 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8851''45''8852''45'absorptive_3340 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         du_'8851''45'absorbs'45''8852'_3294 (coe v0) (coe v1) (coe v2))
      (coe
         du_'8852''45'absorbs'45''8851'_3316 (coe v0) (coe v1) (coe v2))
-- Algebra.Construct.NaturalChoice.MinMaxOp._≥_
d__'8805'__3342 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> ()
d__'8805'__3342 = erased
-- Algebra.Construct.NaturalChoice.MinMaxOp.antimono-≤-distrib-⊓
d_antimono'45''8804''45'distrib'45''8851'_3350 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
d_antimono'45''8804''45'distrib'45''8851'_3350 ~v0 ~v1 ~v2 v3 v4 v5
                                               v6 v7 v8 v9 v10
  = du_antimono'45''8804''45'distrib'45''8851'_3350
      v3 v4 v5 v6 v7 v8 v9 v10
du_antimono'45''8804''45'distrib'45''8851'_3350 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
du_antimono'45''8804''45'distrib'45''8851'_3350 v0 v1 v2 v3 v4 v5
                                                v6 v7
  = let v8
          = coe
              MAlonzo.Code.Relation.Binary.Structures.d_total_142
              (MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                 (coe v0))
              v6 v7 in
    coe
      (case coe v8 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
           -> coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_equalitySubRelation_152)
                (coe
                   v3
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      v6 v7))
                (coe
                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                   (coe v3 v6) (coe v3 v7))
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                      (coe
                         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                         (coe
                            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                            (coe v0))))
                   (coe
                      v3
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         v6 v7))
                   (coe v3 v6)
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                      (coe v3 v6) (coe v3 v7))
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                         (coe
                            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                            (coe
                               MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                               (coe v0))))
                      (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                         (coe
                            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                            (coe
                               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                               (coe
                                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                  (coe v0)))))
                      (coe v3 v6)
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                         (coe v3 v6) (coe v3 v7))
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                         (coe v3 v6) (coe v3 v7))
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                            (coe
                               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                               (coe
                                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                  (coe v0))))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                            (coe v3 v6) (coe v3 v7)))
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8852'y'8776'x_166
                         v2 (coe v3 v6) (coe v3 v7) (coe v5 v6 v7 v9)))
                   (coe
                      v4
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         v6 v7)
                      v6
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_128
                         v1 v6 v7 v9)))
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
           -> coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_equalitySubRelation_152)
                (coe
                   v3
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      v6 v7))
                (coe
                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                   (coe v3 v6) (coe v3 v7))
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                      (coe
                         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                         (coe
                            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                            (coe v0))))
                   (coe
                      v3
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         v6 v7))
                   (coe v3 v7)
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                      (coe v3 v6) (coe v3 v7))
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                         (coe
                            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                            (coe
                               MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                               (coe v0))))
                      (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                         (coe
                            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                            (coe
                               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                               (coe
                                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                  (coe v0)))))
                      (coe v3 v7)
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                         (coe v3 v6) (coe v3 v7))
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                         (coe v3 v6) (coe v3 v7))
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                            (coe
                               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                               (coe
                                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                  (coe v0))))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                            (coe v3 v6) (coe v3 v7)))
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8852'y'8776'y_160
                         v2 (coe v3 v6) (coe v3 v7) (coe v5 v7 v6 v9)))
                   (coe
                      v4
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         v6 v7)
                      v7
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8851'y'8776'y_134
                         v1 v6 v7 v9)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Algebra.Construct.NaturalChoice.MinMaxOp.antimono-≤-distrib-⊔
d_antimono'45''8804''45'distrib'45''8852'_3396 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
d_antimono'45''8804''45'distrib'45''8852'_3396 ~v0 ~v1 ~v2 v3 v4 v5
                                               v6 v7 v8 v9 v10
  = du_antimono'45''8804''45'distrib'45''8852'_3396
      v3 v4 v5 v6 v7 v8 v9 v10
du_antimono'45''8804''45'distrib'45''8852'_3396 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
du_antimono'45''8804''45'distrib'45''8852'_3396 v0 v1 v2 v3 v4 v5
                                                v6 v7
  = let v8
          = coe
              MAlonzo.Code.Relation.Binary.Structures.d_total_142
              (MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                 (coe v0))
              v6 v7 in
    coe
      (case coe v8 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
           -> coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_equalitySubRelation_152)
                (coe
                   v3
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                      v6 v7))
                (coe
                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                   (coe v3 v6) (coe v3 v7))
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                      (coe
                         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                         (coe
                            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                            (coe v0))))
                   (coe
                      v3
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                         v6 v7))
                   (coe v3 v7)
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      (coe v3 v6) (coe v3 v7))
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                         (coe
                            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                            (coe
                               MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                               (coe v0))))
                      (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                         (coe
                            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                            (coe
                               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                               (coe
                                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                  (coe v0)))))
                      (coe v3 v7)
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         (coe v3 v6) (coe v3 v7))
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         (coe v3 v6) (coe v3 v7))
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                            (coe
                               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                               (coe
                                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                  (coe v0))))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                            (coe v3 v6) (coe v3 v7)))
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8851'y'8776'y_134
                         v1 (coe v3 v6) (coe v3 v7) (coe v5 v6 v7 v9)))
                   (coe
                      v4
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                         v6 v7)
                      v7
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8852'y'8776'y_160
                         v2 v6 v7 v9)))
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
           -> coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_equalitySubRelation_152)
                (coe
                   v3
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                      v6 v7))
                (coe
                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                   (coe v3 v6) (coe v3 v7))
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                      (coe
                         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                         (coe
                            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                            (coe v0))))
                   (coe
                      v3
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                         v6 v7))
                   (coe v3 v6)
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      (coe v3 v6) (coe v3 v7))
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                         (coe
                            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                            (coe
                               MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                               (coe v0))))
                      (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                         (coe
                            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                            (coe
                               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                               (coe
                                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                  (coe v0)))))
                      (coe v3 v6)
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         (coe v3 v6) (coe v3 v7))
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         (coe v3 v6) (coe v3 v7))
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                            (coe
                               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                               (coe
                                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                  (coe v0))))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                            (coe v3 v6) (coe v3 v7)))
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_128
                         v1 (coe v3 v6) (coe v3 v7) (coe v5 v7 v6 v9)))
                   (coe
                      v4
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                         v6 v7)
                      v6
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8852'y'8776'x_166
                         v2 v6 v7 v9)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Algebra.Construct.NaturalChoice.MinMaxOp.x⊓y≤x⊔y
d_x'8851'y'8804'x'8852'y_3440 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_x'8851'y'8804'x'8852'y_3440 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7
  = du_x'8851'y'8804'x'8852'y_3440 v3 v4 v5 v6 v7
du_x'8851'y'8804'x'8852'y_3440 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_x'8851'y'8804'x'8852'y_3440 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_start_76
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
               (coe v0))))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
         v3 v4)
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
         v3 v4)
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8764'_302
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8818''45'go_96
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                  (coe v0))))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
            v3 v4)
         v3
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
            v3 v4)
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8764'_302
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8818''45'go_96
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                     (coe v0))))
            v3
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
               v3 v4)
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
               v3 v4)
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                        (coe v0))))
               (coe
                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154 v2
                  v3 v4))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2924
               (coe
                  MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
                  (coe v0))
               (coe
                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
                  (coe v2))
               (coe v3) (coe v4)))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2924
            (coe v0) (coe v1) (coe v3) (coe v4)))
