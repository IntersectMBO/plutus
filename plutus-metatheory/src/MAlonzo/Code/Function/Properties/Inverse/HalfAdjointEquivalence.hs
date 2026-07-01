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

module MAlonzo.Code.Function.Properties.Inverse.HalfAdjointEquivalence where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Function.Bundles

-- Function.Properties.Inverse.HalfAdjointEquivalence._≃_
d__'8771'__24 a0 a1 a2 a3 = ()
data T__'8771'__24
  = C_constructor_78 (AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny)
-- Function.Properties.Inverse.HalfAdjointEquivalence._≃_.to
d_to_46 :: T__'8771'__24 -> AgdaAny -> AgdaAny
d_to_46 v0
  = case coe v0 of
      C_constructor_78 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Properties.Inverse.HalfAdjointEquivalence._≃_.from
d_from_48 :: T__'8771'__24 -> AgdaAny -> AgdaAny
d_from_48 v0
  = case coe v0 of
      C_constructor_78 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Properties.Inverse.HalfAdjointEquivalence._≃_.left-inverse-of
d_left'45'inverse'45'of_52 ::
  T__'8771'__24 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_left'45'inverse'45'of_52 = erased
-- Function.Properties.Inverse.HalfAdjointEquivalence._≃_.right-inverse-of
d_right'45'inverse'45'of_56 ::
  T__'8771'__24 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_right'45'inverse'45'of_56 = erased
-- Function.Properties.Inverse.HalfAdjointEquivalence._≃_.left-right
d_left'45'right_60 ::
  T__'8771'__24 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_left'45'right_60 = erased
-- Function.Properties.Inverse.HalfAdjointEquivalence._≃_.injective
d_injective_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  T__'8771'__24 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_injective_66 = erased
-- Function.Properties.Inverse.HalfAdjointEquivalence.≃⇒↔
d_'8771''8658''8596'_80 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T__'8771'__24 -> MAlonzo.Code.Function.Bundles.T_Inverse_2122
d_'8771''8658''8596'_80 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8771''8658''8596'_80 v4
du_'8771''8658''8596'_80 ::
  T__'8771'__24 -> MAlonzo.Code.Function.Bundles.T_Inverse_2122
du_'8771''8658''8596'_80 v0
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2542
      (coe d_to_46 (coe v0)) (coe d_from_48 (coe v0))
-- Function.Properties.Inverse.HalfAdjointEquivalence._._.from
d_from_90 :: T__'8771'__24 -> AgdaAny -> AgdaAny
d_from_90 v0 = coe d_from_48 (coe v0)
-- Function.Properties.Inverse.HalfAdjointEquivalence._._.injective
d_injective_92 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T__'8771'__24 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_injective_92 = erased
-- Function.Properties.Inverse.HalfAdjointEquivalence._._.left-inverse-of
d_left'45'inverse'45'of_94 ::
  T__'8771'__24 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_left'45'inverse'45'of_94 = erased
-- Function.Properties.Inverse.HalfAdjointEquivalence._._.left-right
d_left'45'right_96 ::
  T__'8771'__24 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_left'45'right_96 = erased
-- Function.Properties.Inverse.HalfAdjointEquivalence._._.right-inverse-of
d_right'45'inverse'45'of_98 ::
  T__'8771'__24 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_right'45'inverse'45'of_98 = erased
-- Function.Properties.Inverse.HalfAdjointEquivalence._._.to
d_to_100 :: T__'8771'__24 -> AgdaAny -> AgdaAny
d_to_100 v0 = coe d_to_46 (coe v0)
-- Function.Properties.Inverse.HalfAdjointEquivalence.↔⇒≃
d_'8596''8658''8771'_102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Inverse_2122 -> T__'8771'__24
d_'8596''8658''8771'_102 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8596''8658''8771'_102 v4
du_'8596''8658''8771'_102 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 -> T__'8771'__24
du_'8596''8658''8771'_102 v0
  = coe
      C_constructor_78 (MAlonzo.Code.Function.Bundles.d_to_2134 (coe v0))
      (MAlonzo.Code.Function.Bundles.d_from_2136 (coe v0))
-- Function.Properties.Inverse.HalfAdjointEquivalence._.A↔B.strictlyInverseʳ
d_strictlyInverse'691'_132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_strictlyInverse'691'_132 = erased
-- Function.Properties.Inverse.HalfAdjointEquivalence._.right-inverse-of
d_right'45'inverse'45'of_194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_right'45'inverse'45'of_194 = erased
-- Function.Properties.Inverse.HalfAdjointEquivalence._.left-right
d_left'45'right_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_left'45'right_200 = erased
-- Function.Properties.Inverse.HalfAdjointEquivalence._._.lemma
d_lemma_208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lemma_208 = erased
