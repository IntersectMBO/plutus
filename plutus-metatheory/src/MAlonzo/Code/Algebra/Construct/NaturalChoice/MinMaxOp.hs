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

module MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Algebra.Bundles qualified
import MAlonzo.Code.Algebra.Bundles.Raw qualified
import MAlonzo.Code.Algebra.Consequences.Setoid qualified
import MAlonzo.Code.Algebra.Construct.NaturalChoice.Base qualified
import MAlonzo.Code.Algebra.Construct.NaturalChoice.MaxOp qualified
import MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp qualified
import MAlonzo.Code.Algebra.Structures qualified
import MAlonzo.Code.Data.Sum.Base qualified
import MAlonzo.Code.Function.Base qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd qualified
import MAlonzo.Code.Relation.Binary.Reasoning.Base.Double qualified
import MAlonzo.Code.Relation.Binary.Reasoning.Syntax qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Algebra.Construct.NaturalChoice.MinMaxOp._._≈_
d__'8776'__24 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__24 = erased
-- Algebra.Construct.NaturalChoice.MinMaxOp._._≲_
d__'8818'__26 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> ()
d__'8818'__26 = erased
-- Algebra.Construct.NaturalChoice.MinMaxOp._._⊓_
d__'8851'__90 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'8851'__90 ~v0 v1 ~v2 = du__'8851'__90 v1
du__'8851'__90 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'8851'__90 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114
      (coe v0)
-- Algebra.Construct.NaturalChoice.MinMaxOp._._Absorbs_
d__Absorbs__106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d__Absorbs__106 = erased
-- Algebra.Construct.NaturalChoice.MinMaxOp._._DistributesOver_
d__DistributesOver__108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d__DistributesOver__108 = erased
-- Algebra.Construct.NaturalChoice.MinMaxOp._._DistributesOverʳ_
d__DistributesOver'691'__110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d__DistributesOver'691'__110 = erased
-- Algebra.Construct.NaturalChoice.MinMaxOp._._DistributesOverˡ_
d__DistributesOver'737'__112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d__DistributesOver'737'__112 = erased
-- Algebra.Construct.NaturalChoice.MinMaxOp._.Absorptive
d_Absorptive_118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Absorptive_118 = erased
-- Algebra.Construct.NaturalChoice.MinMaxOp._.mono-≤-distrib-⊓
d_mono'45''8804''45'distrib'45''8851'_2948 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
d_mono'45''8804''45'distrib'45''8851'_2948 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_mono'45''8804''45'distrib'45''8851'_2948 v3 v4
du_mono'45''8804''45'distrib'45''8851'_2948 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
du_mono'45''8804''45'distrib'45''8851'_2948 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_mono'45''8804''45'distrib'45''8851'_3114
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.x≤y⇒x⊓z≤y
d_x'8804'y'8658'x'8851'z'8804'y_2950 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8658'x'8851'z'8804'y_2950 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_x'8804'y'8658'x'8851'z'8804'y_2950 v3 v4
du_x'8804'y'8658'x'8851'z'8804'y_2950 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'y'8658'x'8851'z'8804'y_2950 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'x'8851'z'8804'y_3160
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.x≤y⇒z⊓x≤y
d_x'8804'y'8658'z'8851'x'8804'y_2952 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8658'z'8851'x'8804'y_2952 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_x'8804'y'8658'z'8851'x'8804'y_2952 v3 v4
du_x'8804'y'8658'z'8851'x'8804'y_2952 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'y'8658'z'8851'x'8804'y_2952 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'z'8851'x'8804'y_3172
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.x≤y⊓z⇒x≤y
d_x'8804'y'8851'z'8658'x'8804'y_2954 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8851'z'8658'x'8804'y_2954 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_x'8804'y'8851'z'8658'x'8804'y_2954 v3 v4
du_x'8804'y'8851'z'8658'x'8804'y_2954 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'y'8851'z'8658'x'8804'y_2954 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'y_3184
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.x≤y⊓z⇒x≤z
d_x'8804'y'8851'z'8658'x'8804'z_2956 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8851'z'8658'x'8804'z_2956 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_x'8804'y'8851'z'8658'x'8804'z_2956 v3 v4
du_x'8804'y'8851'z'8658'x'8804'z_2956 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'y'8851'z'8658'x'8804'z_2956 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'z_3198
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.x⊓y≈x⇒x≤y
d_x'8851'y'8776'x'8658'x'8804'y_2958 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8851'y'8776'x'8658'x'8804'y_2958 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_x'8851'y'8776'x'8658'x'8804'y_2958 v3 v4
du_x'8851'y'8776'x'8658'x'8804'y_2958 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8851'y'8776'x'8658'x'8804'y_2958 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'x'8658'x'8804'y_3068
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.x⊓y≈y⇒y≤x
d_x'8851'y'8776'y'8658'y'8804'x_2960 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8851'y'8776'y'8658'y'8804'x_2960 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_x'8851'y'8776'y'8658'y'8804'x_2960 v3 v4
du_x'8851'y'8776'y'8658'y'8804'x_2960 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8851'y'8776'y'8658'y'8804'x_2960 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'y'8658'y'8804'x_3100
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.x⊓y≤x
d_x'8851'y'8804'x_2962 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_x'8851'y'8804'x_2962 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_x'8851'y'8804'x_2962 v3 v4
du_x'8851'y'8804'x_2962 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_x'8851'y'8804'x_2962 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2808
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.x⊓y≤y
d_x'8851'y'8804'y_2964 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_x'8851'y'8804'y_2964 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_x'8851'y'8804'y_2964 v3 v4
du_x'8851'y'8804'y_2964 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_x'8851'y'8804'y_2964 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2834
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-assoc
d_'8851''45'assoc_2966 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'assoc_2966 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'assoc_2966 v3 v4
du_'8851''45'assoc_2966 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'assoc_2966 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'assoc_2944
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-band
d_'8851''45'band_2968 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Bundles.T_Band_596
d_'8851''45'band_2968 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'band_2968 v3 v4
du_'8851''45'band_2968 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Bundles.T_Band_596
du_'8851''45'band_2968 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'band_3052
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-comm
d_'8851''45'comm_2970 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'comm_2970 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'comm_2970 v3 v4
du_'8851''45'comm_2970 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'comm_2970 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'comm_2856
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-commutativeSemigroup
d_'8851''45'commutativeSemigroup_2972 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662
d_'8851''45'commutativeSemigroup_2972 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'commutativeSemigroup_2972 v3 v4
du_'8851''45'commutativeSemigroup_2972 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662
du_'8851''45'commutativeSemigroup_2972 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'commutativeSemigroup_3054
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-cong
d_'8851''45'cong_2974 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'cong_2974 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'cong_2974 v3 v4
du_'8851''45'cong_2974 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'cong_2974 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong_2930
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-congʳ
d_'8851''45'cong'691'_2976 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'cong'691'_2976 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'cong'691'_2976 v3 v4
du_'8851''45'cong'691'_2976 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'cong'691'_2976 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong'691'_2920
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-congˡ
d_'8851''45'cong'737'_2978 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'cong'737'_2978 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'cong'737'_2978 v3 v4
du_'8851''45'cong'737'_2978 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'cong'737'_2978 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong'737'_2882
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-glb
d_'8851''45'glb_2980 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'glb_2980 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'glb_2980 v3 v4
du_'8851''45'glb_2980 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'glb_2980 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'glb_3278
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-idem
d_'8851''45'idem_2982 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny
d_'8851''45'idem_2982 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'idem_2982 v3 v4
du_'8851''45'idem_2982 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  AgdaAny -> AgdaAny
du_'8851''45'idem_2982 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'idem_2984
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-identity
d_'8851''45'identity_2984 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45'identity_2984 ~v0 v1 ~v2 v3 v4
  = du_'8851''45'identity_2984 v1 v3 v4
du_'8851''45'identity_2984 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8851''45'identity_2984 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         (\ v3 ->
            coe
              MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8851'y'8776'y_126
              v0 v1 v3 (coe v2 v3)))
      (coe
         (\ v3 ->
            coe
              MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_120
              v0 v3 v1 (coe v2 v3)))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-identityʳ
d_'8851''45'identity'691'_2986 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8851''45'identity'691'_2986 ~v0 v1 ~v2 v3 v4 v5
  = du_'8851''45'identity'691'_2986 v1 v3 v4 v5
du_'8851''45'identity'691'_2986 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_'8851''45'identity'691'_2986 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_120
      v0 v3 v1 (coe v2 v3)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-identityˡ
d_'8851''45'identity'737'_2988 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8851''45'identity'737'_2988 ~v0 v1 ~v2 v3 v4 v5
  = du_'8851''45'identity'737'_2988 v1 v3 v4 v5
du_'8851''45'identity'737'_2988 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_'8851''45'identity'737'_2988 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8851'y'8776'y_126
      v0 v1 v3 (coe v2 v3)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-isBand
d_'8851''45'isBand_2990 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
d_'8851''45'isBand_2990 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'isBand_2990 v3 v4
du_'8851''45'isBand_2990 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
du_'8851''45'isBand_2990 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isBand_3034
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-isCommutativeSemigroup
d_'8851''45'isCommutativeSemigroup_2992 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_548
d_'8851''45'isCommutativeSemigroup_2992 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'isCommutativeSemigroup_2992 v3 v4
du_'8851''45'isCommutativeSemigroup_2992 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_548
du_'8851''45'isCommutativeSemigroup_2992 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isCommutativeSemigroup_3036
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-isMagma
d_'8851''45'isMagma_2994 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'8851''45'isMagma_2994 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'isMagma_2994 v3 v4
du_'8851''45'isMagma_2994 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_'8851''45'isMagma_2994 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isMagma_3030
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-isMonoid
d_'8851''45'isMonoid_2996 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_'8851''45'isMonoid_2996 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'isMonoid_2996 v3 v4
du_'8851''45'isMonoid_2996 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
du_'8851''45'isMonoid_2996 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isMonoid_3042
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-isSelectiveMagma
d_'8851''45'isSelectiveMagma_2998 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_436
d_'8851''45'isSelectiveMagma_2998 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'isSelectiveMagma_2998 v3 v4
du_'8851''45'isSelectiveMagma_2998 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_436
du_'8851''45'isSelectiveMagma_2998 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3038
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-isSemigroup
d_'8851''45'isSemigroup_3000 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_'8851''45'isSemigroup_3000 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'isSemigroup_3000 v3 v4
du_'8851''45'isSemigroup_3000 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
du_'8851''45'isSemigroup_3000 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSemigroup_3032
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-magma
d_'8851''45'magma_3002 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_68
d_'8851''45'magma_3002 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'magma_3002 v3 v4
du_'8851''45'magma_3002 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_68
du_'8851''45'magma_3002 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'magma_3048
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-mono-≤
d_'8851''45'mono'45''8804'_3004 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'mono'45''8804'_3004 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'mono'45''8804'_3004 v3 v4
du_'8851''45'mono'45''8804'_3004 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'mono'45''8804'_3004 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'45''8804'_3206
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-monoid
d_'8851''45'monoid_3006 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Algebra.Bundles.T_Monoid_882
d_'8851''45'monoid_3006 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'monoid_3006 v3 v4
du_'8851''45'monoid_3006 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Algebra.Bundles.T_Monoid_882
du_'8851''45'monoid_3006 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'monoid_3060
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-monoʳ-≤
d_'8851''45'mono'691''45''8804'_3008 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'mono'691''45''8804'_3008 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'mono'691''45''8804'_3008 v3 v4
du_'8851''45'mono'691''45''8804'_3008 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'mono'691''45''8804'_3008 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'691''45''8804'_3266
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-monoˡ-≤
d_'8851''45'mono'737''45''8804'_3010 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'mono'737''45''8804'_3010 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'mono'737''45''8804'_3010 v3 v4
du_'8851''45'mono'737''45''8804'_3010 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'mono'737''45''8804'_3010 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'737''45''8804'_3256
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-rawMagma
d_'8851''45'rawMagma_3012 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36
d_'8851''45'rawMagma_3012 ~v0 ~v1 ~v2 ~v3 v4 ~v5
  = du_'8851''45'rawMagma_3012 v4
du_'8851''45'rawMagma_3012 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36
du_'8851''45'rawMagma_3012 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'rawMagma_3046
      (coe v0)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-sel
d_'8851''45'sel_3014 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8851''45'sel_3014 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'sel_3014 v3 v4
du_'8851''45'sel_3014 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'8851''45'sel_3014 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'sel_2988
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-selectiveMagma
d_'8851''45'selectiveMagma_3016 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Bundles.T_SelectiveMagma_122
d_'8851''45'selectiveMagma_3016 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'selectiveMagma_3016 v3 v4
du_'8851''45'selectiveMagma_3016 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Bundles.T_SelectiveMagma_122
du_'8851''45'selectiveMagma_3016 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'selectiveMagma_3056
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-semigroup
d_'8851''45'semigroup_3018 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
d_'8851''45'semigroup_3018 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'semigroup_3018 v3 v4
du_'8851''45'semigroup_3018 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
du_'8851''45'semigroup_3018 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'semigroup_3050
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-triangulate
d_'8851''45'triangulate_3020 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'triangulate_3020 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'triangulate_3020 v3 v4
du_'8851''45'triangulate_3020 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'triangulate_3020 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'triangulate_3292
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-zero
d_'8851''45'zero_3022 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45'zero_3022 ~v0 v1 ~v2 v3 v4
  = du_'8851''45'zero_3022 v1 v3 v4
du_'8851''45'zero_3022 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8851''45'zero_3022 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         (\ v3 ->
            coe
              MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_120
              v0 v1 v3 (coe v2 v3)))
      (coe
         (\ v3 ->
            coe
              MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8851'y'8776'y_126
              v0 v3 v1 (coe v2 v3)))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-zeroʳ
d_'8851''45'zero'691'_3024 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8851''45'zero'691'_3024 ~v0 v1 ~v2 v3 v4 v5
  = du_'8851''45'zero'691'_3024 v1 v3 v4 v5
du_'8851''45'zero'691'_3024 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_'8851''45'zero'691'_3024 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8851'y'8776'y_126
      v0 v3 v1 (coe v2 v3)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-zeroˡ
d_'8851''45'zero'737'_3026 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8851''45'zero'737'_3026 ~v0 v1 ~v2 v3 v4 v5
  = du_'8851''45'zero'737'_3026 v1 v3 v4 v5
du_'8851''45'zero'737'_3026 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_'8851''45'zero'737'_3026 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_120
      v0 v1 v3 (coe v2 v3)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.mono-≤-distrib-⊔
d_mono'45''8804''45'distrib'45''8852'_3030 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
d_mono'45''8804''45'distrib'45''8852'_3030 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_mono'45''8804''45'distrib'45''8852'_3030 v3 v5
du_mono'45''8804''45'distrib'45''8852'_3030 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
du_mono'45''8804''45'distrib'45''8852'_3030 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MaxOp.du_mono'45''8804''45'distrib'45''8852'_182
      (coe v0) (coe v1)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.x⊓y≤x
d_x'8851'y'8804'x_3032 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_x'8851'y'8804'x_3032 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_x'8851'y'8804'x_3032 v3 v5
du_x'8851'y'8804'x_3032 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_x'8851'y'8804'x_3032 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2808
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.x≤y⇒x⊓z≤y
d_x'8804'y'8658'x'8851'z'8804'y_3034 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8658'x'8851'z'8804'y_3034 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_x'8804'y'8658'x'8851'z'8804'y_3034 v3 v5
du_x'8804'y'8658'x'8851'z'8804'y_3034 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'y'8658'x'8851'z'8804'y_3034 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'x'8851'z'8804'y_3160
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.x≤y⇒z⊓x≤y
d_x'8804'y'8658'z'8851'x'8804'y_3036 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8658'z'8851'x'8804'y_3036 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_x'8804'y'8658'z'8851'x'8804'y_3036 v3 v5
du_x'8804'y'8658'z'8851'x'8804'y_3036 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'y'8658'z'8851'x'8804'y_3036 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'z'8851'x'8804'y_3172
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.x⊓y≤y
d_x'8851'y'8804'y_3038 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_x'8851'y'8804'y_3038 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_x'8851'y'8804'y_3038 v3 v5
du_x'8851'y'8804'y_3038 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_x'8851'y'8804'y_3038 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2834
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.x⊓y≈x⇒x≤y
d_x'8851'y'8776'x'8658'x'8804'y_3040 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8851'y'8776'x'8658'x'8804'y_3040 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_x'8851'y'8776'x'8658'x'8804'y_3040 v3 v5
du_x'8851'y'8776'x'8658'x'8804'y_3040 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8851'y'8776'x'8658'x'8804'y_3040 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'x'8658'x'8804'y_3068
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.x⊓y≈y⇒y≤x
d_x'8851'y'8776'y'8658'y'8804'x_3042 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8851'y'8776'y'8658'y'8804'x_3042 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_x'8851'y'8776'y'8658'y'8804'x_3042 v3 v5
du_x'8851'y'8776'y'8658'y'8804'x_3042 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8851'y'8776'y'8658'y'8804'x_3042 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'y'8658'y'8804'x_3100
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.x≤y⊓z⇒x≤y
d_x'8804'y'8851'z'8658'x'8804'y_3044 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8851'z'8658'x'8804'y_3044 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_x'8804'y'8851'z'8658'x'8804'y_3044 v3 v5
du_x'8804'y'8851'z'8658'x'8804'y_3044 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'y'8851'z'8658'x'8804'y_3044 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'y_3184
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.x≤y⊓z⇒x≤z
d_x'8804'y'8851'z'8658'x'8804'z_3046 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8851'z'8658'x'8804'z_3046 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_x'8804'y'8851'z'8658'x'8804'z_3046 v3 v5
du_x'8804'y'8851'z'8658'x'8804'z_3046 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'y'8851'z'8658'x'8804'z_3046 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'z_3198
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-assoc
d_'8851''45'assoc_3048 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'assoc_3048 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'assoc_3048 v3 v5
du_'8851''45'assoc_3048 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'assoc_3048 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'assoc_2944
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-band
d_'8851''45'band_3050 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Bundles.T_Band_596
d_'8851''45'band_3050 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'band_3050 v3 v5
du_'8851''45'band_3050 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Bundles.T_Band_596
du_'8851''45'band_3050 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'band_3052
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-comm
d_'8851''45'comm_3052 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'comm_3052 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'comm_3052 v3 v5
du_'8851''45'comm_3052 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'comm_3052 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'comm_2856
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-commutativeSemigroup
d_'8851''45'commutativeSemigroup_3054 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662
d_'8851''45'commutativeSemigroup_3054 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'commutativeSemigroup_3054 v3 v5
du_'8851''45'commutativeSemigroup_3054 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662
du_'8851''45'commutativeSemigroup_3054 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'commutativeSemigroup_3054
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-cong
d_'8851''45'cong_3056 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'cong_3056 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'cong_3056 v3 v5
du_'8851''45'cong_3056 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'cong_3056 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong_2930
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-congʳ
d_'8851''45'cong'691'_3058 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'cong'691'_3058 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'cong'691'_3058 v3 v5
du_'8851''45'cong'691'_3058 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'cong'691'_3058 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong'691'_2920
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-congˡ
d_'8851''45'cong'737'_3060 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'cong'737'_3060 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'cong'737'_3060 v3 v5
du_'8851''45'cong'737'_3060 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'cong'737'_3060 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong'737'_2882
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-idem
d_'8851''45'idem_3062 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny
d_'8851''45'idem_3062 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'idem_3062 v3 v5
du_'8851''45'idem_3062 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny
du_'8851''45'idem_3062 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'idem_2984
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-identity
d_'8851''45'identity_3064 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45'identity_3064 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_'8851''45'identity_3064 v5 v6 v7
du_'8851''45'identity_3064 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8851''45'identity_3064 v0 v1 v2
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
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-identityʳ
d_'8851''45'identity'691'_3066 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8851''45'identity'691'_3066 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8
  = du_'8851''45'identity'691'_3066 v5 v6 v7 v8
du_'8851''45'identity'691'_3066 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_'8851''45'identity'691'_3066 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8852'y'8776'x_156
      v0 v3 v1 (coe v2 v3)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-identityˡ
d_'8851''45'identity'737'_3068 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8851''45'identity'737'_3068 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8
  = du_'8851''45'identity'737'_3068 v5 v6 v7 v8
du_'8851''45'identity'737'_3068 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_'8851''45'identity'737'_3068 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8852'y'8776'y_150
      v0 v1 v3 (coe v2 v3)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-isBand
d_'8851''45'isBand_3070 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
d_'8851''45'isBand_3070 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'isBand_3070 v3 v5
du_'8851''45'isBand_3070 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
du_'8851''45'isBand_3070 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isBand_3034
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-isCommutativeSemigroup
d_'8851''45'isCommutativeSemigroup_3072 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_548
d_'8851''45'isCommutativeSemigroup_3072 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'isCommutativeSemigroup_3072 v3 v5
du_'8851''45'isCommutativeSemigroup_3072 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_548
du_'8851''45'isCommutativeSemigroup_3072 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isCommutativeSemigroup_3036
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-isMagma
d_'8851''45'isMagma_3074 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'8851''45'isMagma_3074 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'isMagma_3074 v3 v5
du_'8851''45'isMagma_3074 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_'8851''45'isMagma_3074 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isMagma_3030
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-isMonoid
d_'8851''45'isMonoid_3076 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_'8851''45'isMonoid_3076 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'isMonoid_3076 v3 v5
du_'8851''45'isMonoid_3076 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
du_'8851''45'isMonoid_3076 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isMonoid_3042
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-isSelectiveMagma
d_'8851''45'isSelectiveMagma_3078 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_436
d_'8851''45'isSelectiveMagma_3078 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'isSelectiveMagma_3078 v3 v5
du_'8851''45'isSelectiveMagma_3078 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_436
du_'8851''45'isSelectiveMagma_3078 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3038
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-isSemigroup
d_'8851''45'isSemigroup_3080 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_'8851''45'isSemigroup_3080 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'isSemigroup_3080 v3 v5
du_'8851''45'isSemigroup_3080 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
du_'8851''45'isSemigroup_3080 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSemigroup_3032
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-glb
d_'8851''45'glb_3082 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'glb_3082 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'glb_3082 v3 v5
du_'8851''45'glb_3082 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'glb_3082 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'glb_3278
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-magma
d_'8851''45'magma_3084 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_68
d_'8851''45'magma_3084 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'magma_3084 v3 v5
du_'8851''45'magma_3084 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_68
du_'8851''45'magma_3084 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'magma_3048
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-mono-≤
d_'8851''45'mono'45''8804'_3086 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'mono'45''8804'_3086 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'mono'45''8804'_3086 v3 v5
du_'8851''45'mono'45''8804'_3086 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'mono'45''8804'_3086 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'45''8804'_3206
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-monoid
d_'8851''45'monoid_3088 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Algebra.Bundles.T_Monoid_882
d_'8851''45'monoid_3088 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'monoid_3088 v3 v5
du_'8851''45'monoid_3088 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Algebra.Bundles.T_Monoid_882
du_'8851''45'monoid_3088 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'monoid_3060
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-monoʳ-≤
d_'8851''45'mono'691''45''8804'_3090 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'mono'691''45''8804'_3090 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'mono'691''45''8804'_3090 v3 v5
du_'8851''45'mono'691''45''8804'_3090 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'mono'691''45''8804'_3090 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'691''45''8804'_3266
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-monoˡ-≤
d_'8851''45'mono'737''45''8804'_3092 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'mono'737''45''8804'_3092 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'mono'737''45''8804'_3092 v3 v5
du_'8851''45'mono'737''45''8804'_3092 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'mono'737''45''8804'_3092 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'737''45''8804'_3256
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-sel
d_'8851''45'sel_3094 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8851''45'sel_3094 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'sel_3094 v3 v5
du_'8851''45'sel_3094 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'8851''45'sel_3094 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'sel_2988
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-selectiveMagma
d_'8851''45'selectiveMagma_3096 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Bundles.T_SelectiveMagma_122
d_'8851''45'selectiveMagma_3096 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'selectiveMagma_3096 v3 v5
du_'8851''45'selectiveMagma_3096 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Bundles.T_SelectiveMagma_122
du_'8851''45'selectiveMagma_3096 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'selectiveMagma_3056
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-semigroup
d_'8851''45'semigroup_3098 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
d_'8851''45'semigroup_3098 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'semigroup_3098 v3 v5
du_'8851''45'semigroup_3098 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
du_'8851''45'semigroup_3098 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'semigroup_3050
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-triangulate
d_'8851''45'triangulate_3100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'triangulate_3100 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'triangulate_3100 v3 v5
du_'8851''45'triangulate_3100 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'triangulate_3100 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'triangulate_3292
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
         (coe v1))
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-zero
d_'8851''45'zero_3102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45'zero_3102 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_'8851''45'zero_3102 v5 v6 v7
du_'8851''45'zero_3102 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8851''45'zero_3102 v0 v1 v2
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
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-zeroʳ
d_'8851''45'zero'691'_3104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8851''45'zero'691'_3104 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8
  = du_'8851''45'zero'691'_3104 v5 v6 v7 v8
du_'8851''45'zero'691'_3104 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_'8851''45'zero'691'_3104 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8852'y'8776'y_150
      v0 v3 v1 (coe v2 v3)
-- Algebra.Construct.NaturalChoice.MinMaxOp._.⊓-zeroˡ
d_'8851''45'zero'737'_3106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8851''45'zero'737'_3106 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8
  = du_'8851''45'zero'737'_3106 v5 v6 v7 v8
du_'8851''45'zero'737'_3106 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_'8851''45'zero'737'_3106 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8852'y'8776'x_156
      v0 v1 v3 (coe v2 v3)
-- Algebra.Construct.NaturalChoice.MinMaxOp.⊓-distribˡ-⊔
d_'8851''45'distrib'737''45''8852'_3108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'distrib'737''45''8852'_3108 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7
                                        v8
  = du_'8851''45'distrib'737''45''8852'_3108 v3 v4 v5 v6 v7 v8
du_'8851''45'distrib'737''45''8852'_3108 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'distrib'737''45''8852'_3108 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Relation.Binary.Structures.d_total_134
              (MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                 (coe v0))
              v4 v5 in
    coe
      (case coe v6 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
           -> let v8
                    = coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_equalitySubRelation_152 in
              coe
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
                   (coe v8)
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                      v3
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                         v4 v5))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                         v3 v4)
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                         v3 v5))
                   (let v9
                          = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                                 (coe v0)) in
                    coe
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                            (coe v9))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                            v3
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                               v4 v5))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                            v3 v5)
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                               v3 v4)
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                               v3 v5))
                         (let v10
                                = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                                       (coe v0)) in
                          coe
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                               (coe
                                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                                  (coe v10))
                               (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                                  (coe
                                     MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                                     (coe v10)))
                               (coe
                                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114
                                  v1 v3 v5)
                               (coe
                                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144
                                  v2
                                  (coe
                                     MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114
                                     v1 v3 v4)
                                  (coe
                                     MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114
                                     v1 v3 v5))
                               (coe
                                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144
                                  v2
                                  (coe
                                     MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114
                                     v1 v3 v4)
                                  (coe
                                     MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114
                                     v1 v3 v5))
                               (let v11
                                      = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                                             (coe v0)) in
                                coe
                                  (coe
                                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                     (coe
                                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                                        (coe v11))
                                     (coe
                                        MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144
                                        v2
                                        (coe
                                           MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114
                                           v1 v3 v4)
                                        (coe
                                           MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114
                                           v1 v3 v5))))
                               (coe
                                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8852'y'8776'y_150
                                  v2
                                  (coe
                                     MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                     (coe
                                        MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114
                                        v1 v3)
                                     (\ v11 v12 -> v11) v4 v5)
                                  (coe
                                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                     (\ v11 v12 -> v12)
                                     (coe
                                        MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114
                                        v1 v3)
                                     v4 v5)
                                  (coe
                                     MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'691''45''8804'_3266
                                     (coe v0) (coe v1) (coe v3) (coe v4) (coe v5) (coe v7)))))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong'737'_2882
                            (coe v0) (coe v1) (coe v3)
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                               v4 v5)
                            (coe v5)
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8852'y'8776'y_150
                               v2 v4 v5 v7)))))
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
           -> let v8
                    = coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_equalitySubRelation_152 in
              coe
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
                   (coe v8)
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                      v3
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                         v4 v5))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                         v3 v4)
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                         v3 v5))
                   (let v9
                          = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                                 (coe v0)) in
                    coe
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                            (coe v9))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                            v3
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                               v4 v5))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                            v3 v4)
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                               v3 v4)
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                               v3 v5))
                         (let v10
                                = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                                       (coe v0)) in
                          coe
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                               (coe
                                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                                  (coe v10))
                               (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                                  (coe
                                     MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                                     (coe v10)))
                               (coe
                                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114
                                  v1 v3 v4)
                               (coe
                                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144
                                  v2
                                  (coe
                                     MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114
                                     v1 v3 v4)
                                  (coe
                                     MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114
                                     v1 v3 v5))
                               (coe
                                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144
                                  v2
                                  (coe
                                     MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114
                                     v1 v3 v4)
                                  (coe
                                     MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114
                                     v1 v3 v5))
                               (let v11
                                      = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                                             (coe v0)) in
                                coe
                                  (coe
                                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                     (coe
                                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                                        (coe v11))
                                     (coe
                                        MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144
                                        v2
                                        (coe
                                           MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114
                                           v1 v3 v4)
                                        (coe
                                           MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114
                                           v1 v3 v5))))
                               (coe
                                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8852'y'8776'x_156
                                  v2
                                  (coe
                                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                     (\ v11 v12 -> v12)
                                     (coe
                                        MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114
                                        v1 v3)
                                     v5 v4)
                                  (coe
                                     MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                     (coe
                                        MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114
                                        v1 v3)
                                     (\ v11 v12 -> v11) v5 v4)
                                  (coe
                                     MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'691''45''8804'_3266
                                     (coe v0) (coe v1) (coe v3) (coe v5) (coe v4) (coe v7)))))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong'737'_2882
                            (coe v0) (coe v1) (coe v3)
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                               v4 v5)
                            (coe v4)
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8852'y'8776'x_156
                               v2 v4 v5 v7)))))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Algebra.Construct.NaturalChoice.MinMaxOp.⊓-distribʳ-⊔
d_'8851''45'distrib'691''45''8852'_3136 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'distrib'691''45''8852'_3136 ~v0 ~v1 ~v2 v3 v4 v5
  = du_'8851''45'distrib'691''45''8852'_3136 v3 v4 v5
du_'8851''45'distrib'691''45''8852'_3136 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'distrib'691''45''8852'_3136 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Consequences.Setoid.du_comm'43'distr'737''8658'distr'691'_684
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_setoid_180
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_preorder_252 (coe v0)))
      (MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114
         (coe v1))
      (MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144
         (coe v2))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong_2930
         (coe
            MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
            (coe v0))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
            (coe v2)))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'comm_2856
         (coe v0) (coe v1))
      (coe
         du_'8851''45'distrib'737''45''8852'_3108 (coe v0) (coe v1)
         (coe v2))
-- Algebra.Construct.NaturalChoice.MinMaxOp.⊓-distrib-⊔
d_'8851''45'distrib'45''8852'_3138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45'distrib'45''8852'_3138 ~v0 ~v1 ~v2 v3 v4 v5
  = du_'8851''45'distrib'45''8852'_3138 v3 v4 v5
du_'8851''45'distrib'45''8852'_3138 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8851''45'distrib'45''8852'_3138 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         du_'8851''45'distrib'737''45''8852'_3108 (coe v0) (coe v1)
         (coe v2))
      (coe
         du_'8851''45'distrib'691''45''8852'_3136 (coe v0) (coe v1)
         (coe v2))
-- Algebra.Construct.NaturalChoice.MinMaxOp.⊔-distribˡ-⊓
d_'8852''45'distrib'737''45''8851'_3140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8852''45'distrib'737''45''8851'_3140 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7
                                        v8
  = du_'8852''45'distrib'737''45''8851'_3140 v3 v4 v5 v6 v7 v8
du_'8852''45'distrib'737''45''8851'_3140 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8852''45'distrib'737''45''8851'_3140 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Relation.Binary.Structures.d_total_134
              (MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                 (coe v0))
              v4 v5 in
    coe
      (case coe v6 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
           -> let v8
                    = coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_equalitySubRelation_152 in
              coe
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
                   (coe v8)
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                      v3
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                         v4 v5))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                         v3 v4)
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                         v3 v5))
                   (let v9
                          = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                                 (coe v0)) in
                    coe
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                            (coe v9))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                            v3
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                               v4 v5))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                            v3 v4)
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                               v3 v4)
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                               v3 v5))
                         (let v10
                                = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                                       (coe v0)) in
                          coe
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                               (coe
                                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                                  (coe v10))
                               (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                                  (coe
                                     MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                                     (coe v10)))
                               (coe
                                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144
                                  v2 v3 v4)
                               (coe
                                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114
                                  v1
                                  (coe
                                     MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144
                                     v2 v3 v4)
                                  (coe
                                     MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144
                                     v2 v3 v5))
                               (coe
                                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114
                                  v1
                                  (coe
                                     MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144
                                     v2 v3 v4)
                                  (coe
                                     MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144
                                     v2 v3 v5))
                               (let v11
                                      = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                                             (coe v0)) in
                                coe
                                  (coe
                                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                     (coe
                                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                                        (coe v11))
                                     (coe
                                        MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114
                                        v1
                                        (coe
                                           MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144
                                           v2 v3 v4)
                                        (coe
                                           MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144
                                           v2 v3 v5))))
                               (coe
                                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_120
                                  v1
                                  (coe
                                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                     (\ v11 v12 -> v12)
                                     (coe
                                        MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144
                                        v2 v3)
                                     v5 v4)
                                  (coe
                                     MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                     (coe
                                        MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144
                                        v2 v3)
                                     (\ v11 v12 -> v11) v5 v4)
                                  (coe
                                     MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'691''45''8804'_3266
                                     (coe
                                        MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
                                        (coe v0))
                                     (coe
                                        MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
                                        (coe v2))
                                     (coe v3) (coe v5) (coe v4) (coe v7)))))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong'737'_2882
                            (coe
                               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
                               (coe v0))
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
                               (coe v2))
                            (coe v3)
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                               v4 v5)
                            (coe v4)
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_120
                               v1 v4 v5 v7)))))
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
           -> let v8
                    = coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_equalitySubRelation_152 in
              coe
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
                   (coe v8)
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                      v3
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                         v4 v5))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                         v3 v4)
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                         v3 v5))
                   (let v9
                          = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                                 (coe v0)) in
                    coe
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                            (coe v9))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                            v3
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                               v4 v5))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                            v3 v5)
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                               v3 v4)
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                               v3 v5))
                         (let v10
                                = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                                       (coe v0)) in
                          coe
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                               (coe
                                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                                  (coe v10))
                               (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                                  (coe
                                     MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                                     (coe v10)))
                               (coe
                                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144
                                  v2 v3 v5)
                               (coe
                                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114
                                  v1
                                  (coe
                                     MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144
                                     v2 v3 v4)
                                  (coe
                                     MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144
                                     v2 v3 v5))
                               (coe
                                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114
                                  v1
                                  (coe
                                     MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144
                                     v2 v3 v4)
                                  (coe
                                     MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144
                                     v2 v3 v5))
                               (let v11
                                      = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                                             (coe v0)) in
                                coe
                                  (coe
                                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                     (coe
                                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                                        (coe v11))
                                     (coe
                                        MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114
                                        v1
                                        (coe
                                           MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144
                                           v2 v3 v4)
                                        (coe
                                           MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144
                                           v2 v3 v5))))
                               (coe
                                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8851'y'8776'y_126
                                  v1
                                  (coe
                                     MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                     (coe
                                        MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144
                                        v2 v3)
                                     (\ v11 v12 -> v11) v4 v5)
                                  (coe
                                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                     (\ v11 v12 -> v12)
                                     (coe
                                        MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144
                                        v2 v3)
                                     v4 v5)
                                  (coe
                                     MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'691''45''8804'_3266
                                     (coe
                                        MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
                                        (coe v0))
                                     (coe
                                        MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
                                        (coe v2))
                                     (coe v3) (coe v4) (coe v5) (coe v7)))))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong'737'_2882
                            (coe
                               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
                               (coe v0))
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
                               (coe v2))
                            (coe v3)
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                               v4 v5)
                            (coe v5)
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8851'y'8776'y_126
                               v1 v4 v5 v7)))))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Algebra.Construct.NaturalChoice.MinMaxOp.⊔-distribʳ-⊓
d_'8852''45'distrib'691''45''8851'_3168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8852''45'distrib'691''45''8851'_3168 ~v0 ~v1 ~v2 v3 v4 v5
  = du_'8852''45'distrib'691''45''8851'_3168 v3 v4 v5
du_'8852''45'distrib'691''45''8851'_3168 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8852''45'distrib'691''45''8851'_3168 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Consequences.Setoid.du_comm'43'distr'737''8658'distr'691'_684
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_setoid_180
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_preorder_252 (coe v0)))
      (MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144
         (coe v2))
      (MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114
         (coe v1))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong_2930
         (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'comm_2856
         (coe
            MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
            (coe v0))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
            (coe v2)))
      (coe
         du_'8852''45'distrib'737''45''8851'_3140 (coe v0) (coe v1)
         (coe v2))
-- Algebra.Construct.NaturalChoice.MinMaxOp.⊔-distrib-⊓
d_'8852''45'distrib'45''8851'_3170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8852''45'distrib'45''8851'_3170 ~v0 ~v1 ~v2 v3 v4 v5
  = du_'8852''45'distrib'45''8851'_3170 v3 v4 v5
du_'8852''45'distrib'45''8851'_3170 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8852''45'distrib'45''8851'_3170 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         du_'8852''45'distrib'737''45''8851'_3140 (coe v0) (coe v1)
         (coe v2))
      (coe
         du_'8852''45'distrib'691''45''8851'_3168 (coe v0) (coe v1)
         (coe v2))
-- Algebra.Construct.NaturalChoice.MinMaxOp.⊓-absorbs-⊔
d_'8851''45'absorbs'45''8852'_3172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'absorbs'45''8852'_3172 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7
  = du_'8851''45'absorbs'45''8852'_3172 v3 v4 v5 v6 v7
du_'8851''45'absorbs'45''8852'_3172 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'absorbs'45''8852'_3172 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Relation.Binary.Structures.d_total_134
              (MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                 (coe v0))
              v3 v4 in
    coe
      (case coe v5 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
           -> let v7
                    = coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_equalitySubRelation_152 in
              coe
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
                   (coe v7)
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                      v3
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                         v3 v4))
                   (coe v3)
                   (let v8
                          = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                                 (coe v0)) in
                    coe
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                            (coe v8))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                            v3
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                               v3 v4))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                            v3 v4)
                         v3
                         (let v9
                                = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                                       (coe v0)) in
                          coe
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                               (coe
                                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                                  (coe v9))
                               (coe
                                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114
                                  v1 v3 v4)
                               v3 v3
                               (let v10
                                      = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                                             (coe v0)) in
                                coe
                                  (coe
                                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                     (coe
                                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                                        (coe v10))
                                     (coe v3)))
                               (coe
                                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_120
                                  v1 v3 v4 v6)))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong'737'_2882
                            (coe v0) (coe v1) (coe v3)
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                               v3 v4)
                            (coe v4)
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8852'y'8776'y_150
                               v2 v3 v4 v6)))))
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
           -> let v7
                    = coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_equalitySubRelation_152 in
              coe
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
                   (coe v7)
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                      v3
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                         v3 v4))
                   (coe v3)
                   (let v8
                          = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                                 (coe v0)) in
                    coe
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                            (coe v8))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                            v3
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                               v3 v4))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                            v3 v3)
                         v3
                         (let v9
                                = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                                       (coe v0)) in
                          coe
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                               (coe
                                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                                  (coe v9))
                               (coe
                                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114
                                  v1 v3 v3)
                               v3 v3
                               (let v10
                                      = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                                             (coe v0)) in
                                coe
                                  (coe
                                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                     (coe
                                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                                        (coe v10))
                                     (coe v3)))
                               (coe
                                  MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'idem_2984
                                  (coe v0) (coe v1) (coe v3))))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong'737'_2882
                            (coe v0) (coe v1) (coe v3)
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                               v3 v4)
                            (coe v3)
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8852'y'8776'x_156
                               v2 v3 v4 v6)))))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Algebra.Construct.NaturalChoice.MinMaxOp.⊔-absorbs-⊓
d_'8852''45'absorbs'45''8851'_3194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8852''45'absorbs'45''8851'_3194 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7
  = du_'8852''45'absorbs'45''8851'_3194 v3 v4 v5 v6 v7
du_'8852''45'absorbs'45''8851'_3194 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8852''45'absorbs'45''8851'_3194 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Relation.Binary.Structures.d_total_134
              (MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                 (coe v0))
              v3 v4 in
    coe
      (case coe v5 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
           -> let v7
                    = coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_equalitySubRelation_152 in
              coe
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
                   (coe v7)
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                      v3
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                         v3 v4))
                   (coe v3)
                   (let v8
                          = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                                 (coe v0)) in
                    coe
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                            (coe v8))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                            v3
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                               v3 v4))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                            v3 v3)
                         v3
                         (let v9
                                = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                                       (coe v0)) in
                          coe
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                               (coe
                                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                                  (coe v9))
                               (coe
                                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144
                                  v2 v3 v3)
                               v3 v3
                               (let v10
                                      = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                                             (coe v0)) in
                                coe
                                  (coe
                                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                     (coe
                                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                                        (coe v10))
                                     (coe v3)))
                               (coe
                                  MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'idem_2984
                                  (coe
                                     MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
                                     (coe v0))
                                  (coe
                                     MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
                                     (coe v2))
                                  (coe v3))))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong'737'_2882
                            (coe
                               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
                               (coe v0))
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
                               (coe v2))
                            (coe v3)
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                               v3 v4)
                            (coe v3)
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_120
                               v1 v3 v4 v6)))))
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
           -> let v7
                    = coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_equalitySubRelation_152 in
              coe
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
                   (coe v7)
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                      v3
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                         v3 v4))
                   (coe v3)
                   (let v8
                          = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                                 (coe v0)) in
                    coe
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                            (coe v8))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                            v3
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                               v3 v4))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                            v3 v4)
                         v3
                         (let v9
                                = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                                       (coe v0)) in
                          coe
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                               (coe
                                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                                  (coe v9))
                               (coe
                                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144
                                  v2 v3 v4)
                               v3 v3
                               (let v10
                                      = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                                             (coe v0)) in
                                coe
                                  (coe
                                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                     (coe
                                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                                        (coe v10))
                                     (coe v3)))
                               (coe
                                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8852'y'8776'x_156
                                  v2 v3 v4 v6)))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong'737'_2882
                            (coe
                               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
                               (coe v0))
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
                               (coe v2))
                            (coe v3)
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                               v3 v4)
                            (coe v4)
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8851'y'8776'y_126
                               v1 v3 v4 v6)))))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Algebra.Construct.NaturalChoice.MinMaxOp.⊔-⊓-absorptive
d_'8852''45''8851''45'absorptive_3216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8852''45''8851''45'absorptive_3216 ~v0 ~v1 ~v2 v3 v4 v5
  = du_'8852''45''8851''45'absorptive_3216 v3 v4 v5
du_'8852''45''8851''45'absorptive_3216 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8852''45''8851''45'absorptive_3216 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         du_'8852''45'absorbs'45''8851'_3194 (coe v0) (coe v1) (coe v2))
      (coe
         du_'8851''45'absorbs'45''8852'_3172 (coe v0) (coe v1) (coe v2))
-- Algebra.Construct.NaturalChoice.MinMaxOp.⊓-⊔-absorptive
d_'8851''45''8852''45'absorptive_3218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45''8852''45'absorptive_3218 ~v0 ~v1 ~v2 v3 v4 v5
  = du_'8851''45''8852''45'absorptive_3218 v3 v4 v5
du_'8851''45''8852''45'absorptive_3218 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8851''45''8852''45'absorptive_3218 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         du_'8851''45'absorbs'45''8852'_3172 (coe v0) (coe v1) (coe v2))
      (coe
         du_'8852''45'absorbs'45''8851'_3194 (coe v0) (coe v1) (coe v2))
-- Algebra.Construct.NaturalChoice.MinMaxOp._≥_
d__'8805'__3220 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> ()
d__'8805'__3220 = erased
-- Algebra.Construct.NaturalChoice.MinMaxOp.antimono-≤-distrib-⊓
d_antimono'45''8804''45'distrib'45''8851'_3228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
d_antimono'45''8804''45'distrib'45''8851'_3228 ~v0 ~v1 ~v2 v3 v4 v5
                                               v6 v7 v8 v9 v10
  = du_antimono'45''8804''45'distrib'45''8851'_3228
      v3 v4 v5 v6 v7 v8 v9 v10
du_antimono'45''8804''45'distrib'45''8851'_3228 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
du_antimono'45''8804''45'distrib'45''8851'_3228 v0 v1 v2 v3 v4 v5
                                                v6 v7
  = let v8
          = coe
              MAlonzo.Code.Relation.Binary.Structures.d_total_134
              (MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                 (coe v0))
              v6 v7 in
    coe
      (case coe v8 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
           -> let v10
                    = coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_equalitySubRelation_152 in
              coe
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
                   (coe v10)
                   (coe
                      v3
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                         v6 v7))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                      (coe v3 v6) (coe v3 v7))
                   (let v11
                          = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                                 (coe v0)) in
                    coe
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                            (coe v11))
                         (coe
                            v3
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                               v6 v7))
                         (coe v3 v6)
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                            (coe v3 v6) (coe v3 v7))
                         (let v12
                                = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                                       (coe v0)) in
                          coe
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                               (coe
                                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                                  (coe v12))
                               (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                                  (coe
                                     MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                                     (coe v12)))
                               (coe v3 v6)
                               (coe
                                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144
                                  v2 (coe v3 v6) (coe v3 v7))
                               (coe
                                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144
                                  v2 (coe v3 v6) (coe v3 v7))
                               (let v13
                                      = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                                             (coe v0)) in
                                coe
                                  (coe
                                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                     (coe
                                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                                        (coe v13))
                                     (coe
                                        MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144
                                        v2 (coe v3 v6) (coe v3 v7))))
                               (coe
                                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8852'y'8776'x_156
                                  v2 (coe v3 v6) (coe v3 v7) (coe v5 v6 v7 v9))))
                         (coe
                            v4
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                               v6 v7)
                            v6
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_120
                               v1 v6 v7 v9)))))
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
           -> let v10
                    = coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_equalitySubRelation_152 in
              coe
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
                   (coe v10)
                   (coe
                      v3
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                         v6 v7))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                      (coe v3 v6) (coe v3 v7))
                   (let v11
                          = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                                 (coe v0)) in
                    coe
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                            (coe v11))
                         (coe
                            v3
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                               v6 v7))
                         (coe v3 v7)
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                            (coe v3 v6) (coe v3 v7))
                         (let v12
                                = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                                       (coe v0)) in
                          coe
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                               (coe
                                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                                  (coe v12))
                               (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                                  (coe
                                     MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                                     (coe v12)))
                               (coe v3 v7)
                               (coe
                                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144
                                  v2 (coe v3 v6) (coe v3 v7))
                               (coe
                                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144
                                  v2 (coe v3 v6) (coe v3 v7))
                               (let v13
                                      = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                                             (coe v0)) in
                                coe
                                  (coe
                                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                     (coe
                                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                                        (coe v13))
                                     (coe
                                        MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144
                                        v2 (coe v3 v6) (coe v3 v7))))
                               (coe
                                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8852'y'8776'y_150
                                  v2 (coe v3 v6) (coe v3 v7) (coe v5 v7 v6 v9))))
                         (coe
                            v4
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                               v6 v7)
                            v7
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8851'y'8776'y_126
                               v1 v6 v7 v9)))))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Algebra.Construct.NaturalChoice.MinMaxOp.antimono-≤-distrib-⊔
d_antimono'45''8804''45'distrib'45''8852'_3274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
d_antimono'45''8804''45'distrib'45''8852'_3274 ~v0 ~v1 ~v2 v3 v4 v5
                                               v6 v7 v8 v9 v10
  = du_antimono'45''8804''45'distrib'45''8852'_3274
      v3 v4 v5 v6 v7 v8 v9 v10
du_antimono'45''8804''45'distrib'45''8852'_3274 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
du_antimono'45''8804''45'distrib'45''8852'_3274 v0 v1 v2 v3 v4 v5
                                                v6 v7
  = let v8
          = coe
              MAlonzo.Code.Relation.Binary.Structures.d_total_134
              (MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                 (coe v0))
              v6 v7 in
    coe
      (case coe v8 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
           -> let v10
                    = coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_equalitySubRelation_152 in
              coe
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
                   (coe v10)
                   (coe
                      v3
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                         v6 v7))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                      (coe v3 v6) (coe v3 v7))
                   (let v11
                          = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                                 (coe v0)) in
                    coe
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                            (coe v11))
                         (coe
                            v3
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                               v6 v7))
                         (coe v3 v7)
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                            (coe v3 v6) (coe v3 v7))
                         (let v12
                                = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                                       (coe v0)) in
                          coe
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                               (coe
                                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                                  (coe v12))
                               (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                                  (coe
                                     MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                                     (coe v12)))
                               (coe v3 v7)
                               (coe
                                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114
                                  v1 (coe v3 v6) (coe v3 v7))
                               (coe
                                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114
                                  v1 (coe v3 v6) (coe v3 v7))
                               (let v13
                                      = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                                             (coe v0)) in
                                coe
                                  (coe
                                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                     (coe
                                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                                        (coe v13))
                                     (coe
                                        MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114
                                        v1 (coe v3 v6) (coe v3 v7))))
                               (coe
                                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8851'y'8776'y_126
                                  v1 (coe v3 v6) (coe v3 v7) (coe v5 v6 v7 v9))))
                         (coe
                            v4
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                               v6 v7)
                            v7
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8852'y'8776'y_150
                               v2 v6 v7 v9)))))
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
           -> let v10
                    = coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_equalitySubRelation_152 in
              coe
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
                   (coe v10)
                   (coe
                      v3
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                         v6 v7))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                      (coe v3 v6) (coe v3 v7))
                   (let v11
                          = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                                 (coe v0)) in
                    coe
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                            (coe v11))
                         (coe
                            v3
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                               v6 v7))
                         (coe v3 v6)
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                            (coe v3 v6) (coe v3 v7))
                         (let v12
                                = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                                       (coe v0)) in
                          coe
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                               (coe
                                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                                  (coe v12))
                               (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                                  (coe
                                     MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                                     (coe v12)))
                               (coe v3 v6)
                               (coe
                                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114
                                  v1 (coe v3 v6) (coe v3 v7))
                               (coe
                                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114
                                  v1 (coe v3 v6) (coe v3 v7))
                               (let v13
                                      = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                                             (coe v0)) in
                                coe
                                  (coe
                                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                     (coe
                                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                                        (coe v13))
                                     (coe
                                        MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114
                                        v1 (coe v3 v6) (coe v3 v7))))
                               (coe
                                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_120
                                  v1 (coe v3 v6) (coe v3 v7) (coe v5 v7 v6 v9))))
                         (coe
                            v4
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                               v6 v7)
                            v6
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8852'y'8776'x_156
                               v2 v6 v7 v9)))))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Algebra.Construct.NaturalChoice.MinMaxOp.x⊓y≤x⊔y
d_x'8851'y'8804'x'8852'y_3318 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_x'8851'y'8804'x'8852'y_3318 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7
  = du_x'8851'y'8804'x'8852'y_3318 v3 v4 v5 v6 v7
du_x'8851'y'8804'x'8852'y_3318 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_x'8851'y'8804'x'8852'y_3318 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
              (coe
                 MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                 (coe v0)) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_start_76
            (coe v5))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
            v3 v4)
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
            v3 v4)
         (let v6
                = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
                    (coe
                       MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                       (coe v0)) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8764'_300
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8818''45'go_96
                  (coe v6))
               (coe
                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114 v1
                  v3 v4)
               v3
               (coe
                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                  v3 v4)
               (let v7
                      = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
                          (coe
                             MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                             (coe v0)) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8764'_300
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8818''45'go_96
                        (coe v7))
                     v3
                     (coe
                        MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                        v3 v4)
                     (coe
                        MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                        v3 v4)
                     (let v8
                            = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
                                (coe
                                   MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
                                   (coe v0)) in
                      coe
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                              (coe v8))
                           (coe
                              MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__144 v2
                              v3 v4)))
                     (coe
                        MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2808
                        (coe
                           MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
                           (coe v0))
                        (coe
                           MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
                           (coe v2))
                        (coe v3) (coe v4))))
               (coe
                  MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2808
                  (coe v0) (coe v1) (coe v3) (coe v4)))))
