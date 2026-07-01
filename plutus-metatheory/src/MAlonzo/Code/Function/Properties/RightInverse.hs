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

module MAlonzo.Code.Function.Properties.RightInverse where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Function.Bundles
import qualified MAlonzo.Code.Function.Consequences
import qualified MAlonzo.Code.Function.Structures
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Function.Properties.RightInverse._.Eq₁._≈_
d__'8776'__44 ::
  T_GeneralizeTel_487 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__44 = erased
-- Function.Properties.RightInverse._.Eq₂._≈_
d__'8776'__70 ::
  T_GeneralizeTel_487 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__70 = erased
-- Function.Properties.RightInverse.mkRightInverse
d_mkRightInverse_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036
d_mkRightInverse_94 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du_mkRightInverse_94 v6 v7
du_mkRightInverse_94 ::
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036
du_mkRightInverse_94 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_2120
      (coe MAlonzo.Code.Function.Bundles.d_to_1868 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_from_1870 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_1872 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_from'45'cong_1874 (coe v0))
      (coe v1)
-- Function.Properties.RightInverse.RightInverse⇒LeftInverse
d_RightInverse'8658'LeftInverse_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1942
d_RightInverse'8658'LeftInverse_172 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_RightInverse'8658'LeftInverse_172 v6
du_RightInverse'8658'LeftInverse_172 ::
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1942
du_RightInverse'8658'LeftInverse_172 v0
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_2034
      (coe MAlonzo.Code.Function.Bundles.d_from_2050 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_to_2048 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_from'45'cong_2054 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_2052 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_inverse'691'_2056 (coe v0))
-- Function.Properties.RightInverse.LeftInverse⇒RightInverse
d_LeftInverse'8658'RightInverse_252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1942 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036
d_LeftInverse'8658'RightInverse_252 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_LeftInverse'8658'RightInverse_252 v6
du_LeftInverse'8658'RightInverse_252 ::
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1942 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036
du_LeftInverse'8658'RightInverse_252 v0
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_2120
      (coe MAlonzo.Code.Function.Bundles.d_from_1956 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_to_1954 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_from'45'cong_1960 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_1958 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_inverse'737'_1962 (coe v0))
-- Function.Properties.RightInverse.RightInverse⇒Surjection
d_RightInverse'8658'Surjection_338 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918
d_RightInverse'8658'Surjection_338 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_RightInverse'8658'Surjection_338 v6
du_RightInverse'8658'Surjection_338 ::
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918
du_RightInverse'8658'Surjection_338 v0
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_1002
      (coe MAlonzo.Code.Function.Bundles.d_from_2050 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_from'45'cong_2054 (coe v0))
      (coe
         MAlonzo.Code.Function.Consequences.du_inverse'737''8658'surjective_38
         (coe MAlonzo.Code.Function.Bundles.d_to_2048 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_inverse'691'_2056 (coe v0)))
-- Function.Properties.RightInverse.↪⇒↠
d_'8618''8658''8608'_418 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918
d_'8618''8658''8608'_418 ~v0 ~v1 ~v2 ~v3
  = du_'8618''8658''8608'_418
du_'8618''8658''8608'_418 ::
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918
du_'8618''8658''8608'_418 = coe du_RightInverse'8658'Surjection_338
-- Function.Properties.RightInverse.↪⇒↩
d_'8618''8658''8617'_420 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1942
d_'8618''8658''8617'_420 ~v0 ~v1 ~v2 ~v3
  = du_'8618''8658''8617'_420
du_'8618''8658''8617'_420 ::
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1942
du_'8618''8658''8617'_420
  = coe du_RightInverse'8658'LeftInverse_172
-- Function.Properties.RightInverse.↩⇒↪
d_'8617''8658''8618'_422 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1942 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036
d_'8617''8658''8618'_422 ~v0 ~v1 ~v2 ~v3
  = du_'8617''8658''8618'_422
du_'8617''8658''8618'_422 ::
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1942 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036
du_'8617''8658''8618'_422
  = coe du_LeftInverse'8658'RightInverse_252
-- Function.Properties.RightInverse._._.Eq₁._≈_
d__'8776'__456 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__456 = erased
-- Function.Properties.RightInverse..generalizedField-S.a
d_'46'generalizedField'45'S'46'a_475 ::
  T_GeneralizeTel_487 -> MAlonzo.Code.Agda.Primitive.T_Level_18
d_'46'generalizedField'45'S'46'a_475 v0
  = case coe v0 of
      C_mkGeneralizeTel_489 v1 v2 v3 v4 v5 v6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Properties.RightInverse..generalizedField-S.ℓ₁
d_'46'generalizedField'45'S'46'ℓ'8321'_477 ::
  T_GeneralizeTel_487 -> MAlonzo.Code.Agda.Primitive.T_Level_18
d_'46'generalizedField'45'S'46'ℓ'8321'_477 v0
  = case coe v0 of
      C_mkGeneralizeTel_489 v1 v2 v3 v4 v5 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Properties.RightInverse..generalizedField-S
d_'46'generalizedField'45'S_479 ::
  T_GeneralizeTel_487 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_'46'generalizedField'45'S_479 v0
  = case coe v0 of
      C_mkGeneralizeTel_489 v1 v2 v3 v4 v5 v6 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Properties.RightInverse..generalizedField-T.a
d_'46'generalizedField'45'T'46'a_481 ::
  T_GeneralizeTel_487 -> MAlonzo.Code.Agda.Primitive.T_Level_18
d_'46'generalizedField'45'T'46'a_481 v0
  = case coe v0 of
      C_mkGeneralizeTel_489 v1 v2 v3 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Properties.RightInverse._._.Eq₂._≈_
d__'8776'__482 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__482 = erased
-- Function.Properties.RightInverse..generalizedField-T.ℓ₁
d_'46'generalizedField'45'T'46'ℓ'8321'_483 ::
  T_GeneralizeTel_487 -> MAlonzo.Code.Agda.Primitive.T_Level_18
d_'46'generalizedField'45'T'46'ℓ'8321'_483 v0
  = case coe v0 of
      C_mkGeneralizeTel_489 v1 v2 v3 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Properties.RightInverse..generalizedField-T
d_'46'generalizedField'45'T_485 ::
  T_GeneralizeTel_487 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_'46'generalizedField'45'T_485 v0
  = case coe v0 of
      C_mkGeneralizeTel_489 v1 v2 v3 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Properties.RightInverse.GeneralizeTel
d_GeneralizeTel_487 = ()
data T_GeneralizeTel_487
  = C_mkGeneralizeTel_489 MAlonzo.Code.Agda.Primitive.T_Level_18
                          MAlonzo.Code.Agda.Primitive.T_Level_18
                          MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
                          MAlonzo.Code.Agda.Primitive.T_Level_18
                          MAlonzo.Code.Agda.Primitive.T_Level_18
                          MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
-- Function.Properties.RightInverse._.to-from
d_to'45'from_510 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_to'45'from_510 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 v7 v8 v9
  = du_to'45'from_510 v2 v5 v6 v7 v8 v9
du_to'45'from_510 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_to'45'from_510 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v0))
      (coe
         MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
         (MAlonzo.Code.Function.Bundles.d_from_2050 (coe v2))
         (\ v6 v7 -> v6) v4
         (coe MAlonzo.Code.Function.Bundles.d_to_2048 v2 v3))
      (coe
         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
         (\ v6 v7 -> v7)
         (MAlonzo.Code.Function.Bundles.d_from_2050 (coe v2)) v4
         (coe MAlonzo.Code.Function.Bundles.d_to_2048 v2 v3))
      v3
      (coe
         MAlonzo.Code.Function.Bundles.d_from'45'cong_2054 v2 v4
         (coe MAlonzo.Code.Function.Bundles.d_to_2048 v2 v3)
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_38
            (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v1))
            (coe MAlonzo.Code.Function.Bundles.d_to_2048 v2 v3) v4 v5))
      (coe
         MAlonzo.Code.Function.Structures.du_strictlyInverse'691'_516
         (coe MAlonzo.Code.Function.Bundles.d_to_2048 (coe v2))
         (coe
            MAlonzo.Code.Function.Bundles.du_isRightInverse_2060 (coe v0)
            (coe v1) (coe v2))
         (coe v3))
