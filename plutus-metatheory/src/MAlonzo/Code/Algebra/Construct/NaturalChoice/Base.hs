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

module MAlonzo.Code.Algebra.Construct.NaturalChoice.Base where

import Data.Text qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Algebra.Construct.NaturalChoice.Base._._≥_
d__'8805'__96 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  AgdaAny -> AgdaAny -> ()
d__'8805'__96 = erased
-- Algebra.Construct.NaturalChoice.Base._.MinOperator
d_MinOperator_98 a0 a1 a2 a3 = ()
data T_MinOperator_98
  = C_MinOperator'46'constructor_1121 (AgdaAny -> AgdaAny -> AgdaAny)
                                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Construct.NaturalChoice.Base._.MinOperator._⊓_
d__'8851'__114 :: T_MinOperator_98 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8851'__114 v0
  = case coe v0 of
      C_MinOperator'46'constructor_1121 v1 v2 v3 -> coe v1
      _                                          -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Construct.NaturalChoice.Base._.MinOperator.x≤y⇒x⊓y≈x
d_x'8804'y'8658'x'8851'y'8776'x_120 ::
  T_MinOperator_98 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8658'x'8851'y'8776'x_120 v0
  = case coe v0 of
      C_MinOperator'46'constructor_1121 v1 v2 v3 -> coe v2
      _                                          -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Construct.NaturalChoice.Base._.MinOperator.x≥y⇒x⊓y≈y
d_x'8805'y'8658'x'8851'y'8776'y_126 ::
  T_MinOperator_98 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8805'y'8658'x'8851'y'8776'y_126 v0
  = case coe v0 of
      C_MinOperator'46'constructor_1121 v1 v2 v3 -> coe v3
      _                                          -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Construct.NaturalChoice.Base._.MaxOperator
d_MaxOperator_128 a0 a1 a2 a3 = ()
data T_MaxOperator_128
  = C_MaxOperator'46'constructor_1665 (AgdaAny -> AgdaAny -> AgdaAny)
                                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Construct.NaturalChoice.Base._.MaxOperator._⊔_
d__'8852'__144 ::
  T_MaxOperator_128 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8852'__144 v0
  = case coe v0 of
      C_MaxOperator'46'constructor_1665 v1 v2 v3 -> coe v1
      _                                          -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Construct.NaturalChoice.Base._.MaxOperator.x≤y⇒x⊔y≈y
d_x'8804'y'8658'x'8852'y'8776'y_150 ::
  T_MaxOperator_128 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8658'x'8852'y'8776'y_150 v0
  = case coe v0 of
      C_MaxOperator'46'constructor_1665 v1 v2 v3 -> coe v2
      _                                          -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Construct.NaturalChoice.Base._.MaxOperator.x≥y⇒x⊔y≈x
d_x'8805'y'8658'x'8852'y'8776'x_156 ::
  T_MaxOperator_128 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8805'y'8658'x'8852'y'8776'x_156 v0
  = case coe v0 of
      C_MaxOperator'46'constructor_1665 v1 v2 v3 -> coe v3
      _                                          -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Construct.NaturalChoice.Base.MinOp⇒MaxOp
d_MinOp'8658'MaxOp_158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  T_MinOperator_98 -> T_MaxOperator_128
d_MinOp'8658'MaxOp_158 ~v0 ~v1 ~v2 ~v3 v4
  = du_MinOp'8658'MaxOp_158 v4
du_MinOp'8658'MaxOp_158 :: T_MinOperator_98 -> T_MaxOperator_128
du_MinOp'8658'MaxOp_158 v0
  = coe
      C_MaxOperator'46'constructor_1665 (coe d__'8851'__114 (coe v0))
      (coe d_x'8805'y'8658'x'8851'y'8776'y_126 (coe v0))
      (coe d_x'8804'y'8658'x'8851'y'8776'x_120 (coe v0))
-- Algebra.Construct.NaturalChoice.Base._._._⊓_
d__'8851'__168 :: T_MinOperator_98 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8851'__168 v0 = coe d__'8851'__114 (coe v0)
-- Algebra.Construct.NaturalChoice.Base._._.x≤y⇒x⊓y≈x
d_x'8804'y'8658'x'8851'y'8776'x_170 ::
  T_MinOperator_98 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8658'x'8851'y'8776'x_170 v0
  = coe d_x'8804'y'8658'x'8851'y'8776'x_120 (coe v0)
-- Algebra.Construct.NaturalChoice.Base._._.x≥y⇒x⊓y≈y
d_x'8805'y'8658'x'8851'y'8776'y_172 ::
  T_MinOperator_98 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8805'y'8658'x'8851'y'8776'y_172 v0
  = coe d_x'8805'y'8658'x'8851'y'8776'y_126 (coe v0)
-- Algebra.Construct.NaturalChoice.Base.MaxOp⇒MinOp
d_MaxOp'8658'MinOp_174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  T_MaxOperator_128 -> T_MinOperator_98
d_MaxOp'8658'MinOp_174 ~v0 ~v1 ~v2 ~v3 v4
  = du_MaxOp'8658'MinOp_174 v4
du_MaxOp'8658'MinOp_174 :: T_MaxOperator_128 -> T_MinOperator_98
du_MaxOp'8658'MinOp_174 v0
  = coe
      C_MinOperator'46'constructor_1121 (coe d__'8852'__144 (coe v0))
      (coe d_x'8805'y'8658'x'8852'y'8776'x_156 (coe v0))
      (coe d_x'8804'y'8658'x'8852'y'8776'y_150 (coe v0))
-- Algebra.Construct.NaturalChoice.Base._._._⊔_
d__'8852'__184 ::
  T_MaxOperator_128 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8852'__184 v0 = coe d__'8852'__144 (coe v0)
-- Algebra.Construct.NaturalChoice.Base._._.x≤y⇒x⊔y≈y
d_x'8804'y'8658'x'8852'y'8776'y_186 ::
  T_MaxOperator_128 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8658'x'8852'y'8776'y_186 v0
  = coe d_x'8804'y'8658'x'8852'y'8776'y_150 (coe v0)
-- Algebra.Construct.NaturalChoice.Base._._.x≥y⇒x⊔y≈x
d_x'8805'y'8658'x'8852'y'8776'x_188 ::
  T_MaxOperator_128 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8805'y'8658'x'8852'y'8776'x_188 v0
  = coe d_x'8805'y'8658'x'8852'y'8776'x_156 (coe v0)
