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

module MAlonzo.Code.Algebra.Construct.NaturalChoice.Base where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Relation.Binary.Bundles

-- Algebra.Construct.NaturalChoice.Base._._≥_
d__'8805'__104 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  AgdaAny -> AgdaAny -> ()
d__'8805'__104 = erased
-- Algebra.Construct.NaturalChoice.Base._.MinOperator
d_MinOperator_106 a0 a1 a2 a3 = ()
data T_MinOperator_106
  = C_constructor_136 (AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Construct.NaturalChoice.Base._.MinOperator._⊓_
d__'8851'__122 ::
  T_MinOperator_106 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8851'__122 v0
  = case coe v0 of
      C_constructor_136 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Construct.NaturalChoice.Base._.MinOperator.x≤y⇒x⊓y≈x
d_x'8804'y'8658'x'8851'y'8776'x_128 ::
  T_MinOperator_106 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8658'x'8851'y'8776'x_128 v0
  = case coe v0 of
      C_constructor_136 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Construct.NaturalChoice.Base._.MinOperator.x≥y⇒x⊓y≈y
d_x'8805'y'8658'x'8851'y'8776'y_134 ::
  T_MinOperator_106 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8805'y'8658'x'8851'y'8776'y_134 v0
  = case coe v0 of
      C_constructor_136 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Construct.NaturalChoice.Base._.MaxOperator
d_MaxOperator_138 a0 a1 a2 a3 = ()
data T_MaxOperator_138
  = C_constructor_168 (AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Construct.NaturalChoice.Base._.MaxOperator._⊔_
d__'8852'__154 ::
  T_MaxOperator_138 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8852'__154 v0
  = case coe v0 of
      C_constructor_168 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Construct.NaturalChoice.Base._.MaxOperator.x≤y⇒x⊔y≈y
d_x'8804'y'8658'x'8852'y'8776'y_160 ::
  T_MaxOperator_138 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8658'x'8852'y'8776'y_160 v0
  = case coe v0 of
      C_constructor_168 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Construct.NaturalChoice.Base._.MaxOperator.x≥y⇒x⊔y≈x
d_x'8805'y'8658'x'8852'y'8776'x_166 ::
  T_MaxOperator_138 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8805'y'8658'x'8852'y'8776'x_166 v0
  = case coe v0 of
      C_constructor_168 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Construct.NaturalChoice.Base.MinOp⇒MaxOp
d_MinOp'8658'MaxOp_170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  T_MinOperator_106 -> T_MaxOperator_138
d_MinOp'8658'MaxOp_170 ~v0 ~v1 ~v2 ~v3 v4
  = du_MinOp'8658'MaxOp_170 v4
du_MinOp'8658'MaxOp_170 :: T_MinOperator_106 -> T_MaxOperator_138
du_MinOp'8658'MaxOp_170 v0
  = coe
      C_constructor_168 (coe d__'8851'__122 (coe v0))
      (coe d_x'8805'y'8658'x'8851'y'8776'y_134 (coe v0))
      (coe d_x'8804'y'8658'x'8851'y'8776'x_128 (coe v0))
-- Algebra.Construct.NaturalChoice.Base._._._⊓_
d__'8851'__180 ::
  T_MinOperator_106 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8851'__180 v0 = coe d__'8851'__122 (coe v0)
-- Algebra.Construct.NaturalChoice.Base._._.x≤y⇒x⊓y≈x
d_x'8804'y'8658'x'8851'y'8776'x_182 ::
  T_MinOperator_106 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8658'x'8851'y'8776'x_182 v0
  = coe d_x'8804'y'8658'x'8851'y'8776'x_128 (coe v0)
-- Algebra.Construct.NaturalChoice.Base._._.x≥y⇒x⊓y≈y
d_x'8805'y'8658'x'8851'y'8776'y_184 ::
  T_MinOperator_106 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8805'y'8658'x'8851'y'8776'y_184 v0
  = coe d_x'8805'y'8658'x'8851'y'8776'y_134 (coe v0)
-- Algebra.Construct.NaturalChoice.Base.MaxOp⇒MinOp
d_MaxOp'8658'MinOp_186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  T_MaxOperator_138 -> T_MinOperator_106
d_MaxOp'8658'MinOp_186 ~v0 ~v1 ~v2 ~v3 v4
  = du_MaxOp'8658'MinOp_186 v4
du_MaxOp'8658'MinOp_186 :: T_MaxOperator_138 -> T_MinOperator_106
du_MaxOp'8658'MinOp_186 v0
  = coe
      C_constructor_136 (coe d__'8852'__154 (coe v0))
      (coe d_x'8805'y'8658'x'8852'y'8776'x_166 (coe v0))
      (coe d_x'8804'y'8658'x'8852'y'8776'y_160 (coe v0))
-- Algebra.Construct.NaturalChoice.Base._._._⊔_
d__'8852'__196 ::
  T_MaxOperator_138 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8852'__196 v0 = coe d__'8852'__154 (coe v0)
-- Algebra.Construct.NaturalChoice.Base._._.x≤y⇒x⊔y≈y
d_x'8804'y'8658'x'8852'y'8776'y_198 ::
  T_MaxOperator_138 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8658'x'8852'y'8776'y_198 v0
  = coe d_x'8804'y'8658'x'8852'y'8776'y_160 (coe v0)
-- Algebra.Construct.NaturalChoice.Base._._.x≥y⇒x⊔y≈x
d_x'8805'y'8658'x'8852'y'8776'x_200 ::
  T_MaxOperator_138 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8805'y'8658'x'8852'y'8776'x_200 v0
  = coe d_x'8805'y'8658'x'8852'y'8776'x_166 (coe v0)
