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

module MAlonzo.Code.Function.Properties.RightInverse where

import Data.Text qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Function.Base qualified
import MAlonzo.Code.Function.Bundles qualified
import MAlonzo.Code.Function.Consequences qualified
import MAlonzo.Code.Function.Structures qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Function.Properties.RightInverse._.Eq₁._≈_
d__'8776'__44 ::
  T_GeneralizeTel_407 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__44 = erased
-- Function.Properties.RightInverse._.Eq₂._≈_
d__'8776'__68 ::
  T_GeneralizeTel_407 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__68 = erased
-- Function.Properties.RightInverse.mkRightInverse
d_mkRightInverse_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880
d_mkRightInverse_90 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du_mkRightInverse_90 v6 v7
du_mkRightInverse_90 ::
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880
du_mkRightInverse_90 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_RightInverse'46'constructor_34573
      (coe MAlonzo.Code.Function.Bundles.d_to_1724 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_from_1726 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_1728 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_from'45'cong_1730 (coe v0))
      (coe v1)
-- Function.Properties.RightInverse.RightInverse⇒LeftInverse
d_RightInverse'8658'LeftInverse_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792
d_RightInverse'8658'LeftInverse_164 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_RightInverse'8658'LeftInverse_164 v6
du_RightInverse'8658'LeftInverse_164 ::
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792
du_RightInverse'8658'LeftInverse_164 v0
  = coe
      MAlonzo.Code.Function.Bundles.C_LeftInverse'46'constructor_29775
      (coe MAlonzo.Code.Function.Bundles.d_from_1894 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_to_1892 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_from'45'cong_1898 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_1896 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_inverse'691'_1900 (coe v0))
-- Function.Properties.RightInverse.LeftInverse⇒RightInverse
d_LeftInverse'8658'RightInverse_240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880
d_LeftInverse'8658'RightInverse_240 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_LeftInverse'8658'RightInverse_240 v6
du_LeftInverse'8658'RightInverse_240 ::
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880
du_LeftInverse'8658'RightInverse_240 v0
  = coe
      MAlonzo.Code.Function.Bundles.C_RightInverse'46'constructor_34573
      (coe MAlonzo.Code.Function.Bundles.d_from_1806 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_to_1804 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_from'45'cong_1810 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_1808 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_inverse'737'_1812 (coe v0))
-- Function.Properties.RightInverse.RightInverse⇒Surjection
d_RightInverse'8658'Surjection_322 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846
d_RightInverse'8658'Surjection_322 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_RightInverse'8658'Surjection_322 v6
du_RightInverse'8658'Surjection_322 ::
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846
du_RightInverse'8658'Surjection_322 v0
  = coe
      MAlonzo.Code.Function.Bundles.C_Surjection'46'constructor_11197
      (coe MAlonzo.Code.Function.Bundles.d_from_1894 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_from'45'cong_1898 (coe v0))
      (coe
         MAlonzo.Code.Function.Consequences.du_inverse'737''8658'surjective_38
         (coe MAlonzo.Code.Function.Bundles.d_to_1892 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_inverse'691'_1900 (coe v0)))
-- Function.Properties.RightInverse..generalizedField-S.a
d_'46'generalizedField'45'S'46'a_395 ::
  T_GeneralizeTel_407 -> MAlonzo.Code.Agda.Primitive.T_Level_18
d_'46'generalizedField'45'S'46'a_395 v0
  = case coe v0 of
      C_mkGeneralizeTel_409 v1 v2 v3 v4 v5 v6 -> coe v1
      _                                       -> MAlonzo.RTE.mazUnreachableError
-- Function.Properties.RightInverse..generalizedField-S.ℓ₁
d_'46'generalizedField'45'S'46'ℓ'8321'_397 ::
  T_GeneralizeTel_407 -> MAlonzo.Code.Agda.Primitive.T_Level_18
d_'46'generalizedField'45'S'46'ℓ'8321'_397 v0
  = case coe v0 of
      C_mkGeneralizeTel_409 v1 v2 v3 v4 v5 v6 -> coe v2
      _                                       -> MAlonzo.RTE.mazUnreachableError
-- Function.Properties.RightInverse.↪⇒↠
d_'8618''8658''8608'_398 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846
d_'8618''8658''8608'_398 ~v0 ~v1 ~v2 ~v3
  = du_'8618''8658''8608'_398
du_'8618''8658''8608'_398 ::
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846
du_'8618''8658''8608'_398 = coe du_RightInverse'8658'Surjection_322
-- Function.Properties.RightInverse..generalizedField-S
d_'46'generalizedField'45'S_399 ::
  T_GeneralizeTel_407 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_'46'generalizedField'45'S_399 v0
  = case coe v0 of
      C_mkGeneralizeTel_409 v1 v2 v3 v4 v5 v6 -> coe v3
      _                                       -> MAlonzo.RTE.mazUnreachableError
-- Function.Properties.RightInverse.↪⇒↩
d_'8618''8658''8617'_400 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792
d_'8618''8658''8617'_400 ~v0 ~v1 ~v2 ~v3
  = du_'8618''8658''8617'_400
du_'8618''8658''8617'_400 ::
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792
du_'8618''8658''8617'_400
  = coe du_RightInverse'8658'LeftInverse_164
-- Function.Properties.RightInverse..generalizedField-T.a
d_'46'generalizedField'45'T'46'a_401 ::
  T_GeneralizeTel_407 -> MAlonzo.Code.Agda.Primitive.T_Level_18
d_'46'generalizedField'45'T'46'a_401 v0
  = case coe v0 of
      C_mkGeneralizeTel_409 v1 v2 v3 v4 v5 v6 -> coe v4
      _                                       -> MAlonzo.RTE.mazUnreachableError
-- Function.Properties.RightInverse.↩⇒↪
d_'8617''8658''8618'_402 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880
d_'8617''8658''8618'_402 ~v0 ~v1 ~v2 ~v3
  = du_'8617''8658''8618'_402
du_'8617''8658''8618'_402 ::
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880
du_'8617''8658''8618'_402
  = coe du_LeftInverse'8658'RightInverse_240
-- Function.Properties.RightInverse..generalizedField-T.ℓ₁
d_'46'generalizedField'45'T'46'ℓ'8321'_403 ::
  T_GeneralizeTel_407 -> MAlonzo.Code.Agda.Primitive.T_Level_18
d_'46'generalizedField'45'T'46'ℓ'8321'_403 v0
  = case coe v0 of
      C_mkGeneralizeTel_409 v1 v2 v3 v4 v5 v6 -> coe v5
      _                                       -> MAlonzo.RTE.mazUnreachableError
-- Function.Properties.RightInverse..generalizedField-T
d_'46'generalizedField'45'T_405 ::
  T_GeneralizeTel_407 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_'46'generalizedField'45'T_405 v0
  = case coe v0 of
      C_mkGeneralizeTel_409 v1 v2 v3 v4 v5 v6 -> coe v6
      _                                       -> MAlonzo.RTE.mazUnreachableError
-- Function.Properties.RightInverse.GeneralizeTel
d_GeneralizeTel_407 = ()
data T_GeneralizeTel_407
  = C_mkGeneralizeTel_409 MAlonzo.Code.Agda.Primitive.T_Level_18
                          MAlonzo.Code.Agda.Primitive.T_Level_18
                          MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
                          MAlonzo.Code.Agda.Primitive.T_Level_18
                          MAlonzo.Code.Agda.Primitive.T_Level_18
                          MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
-- Function.Properties.RightInverse._._.Eq₁._≈_
d__'8776'__436 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__436 = erased
-- Function.Properties.RightInverse._._.Eq₂._≈_
d__'8776'__460 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__460 = erased
-- Function.Properties.RightInverse._.to-from
d_to'45'from_486 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_to'45'from_486 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 v7 v8 v9
  = du_to'45'from_486 v2 v5 v6 v7 v8 v9
du_to'45'from_486 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_to'45'from_486 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Function.Bundles.du_isRightInverse_1904 (coe v0)
              (coe v1) (coe v2) in
    coe
      (let v7
             = MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v6) in
       coe
         (let v8
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v7) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v8))
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (MAlonzo.Code.Function.Bundles.d_from_1894 (coe v2))
                  (\ v9 v10 -> v9) v4
                  (coe MAlonzo.Code.Function.Bundles.d_to_1892 v2 v3))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v9 v10 -> v10)
                  (MAlonzo.Code.Function.Bundles.d_from_1894 (coe v2)) v4
                  (coe MAlonzo.Code.Function.Bundles.d_to_1892 v2 v3))
               v3
               (coe
                  MAlonzo.Code.Function.Bundles.d_from'45'cong_1898 v2 v4
                  (coe MAlonzo.Code.Function.Bundles.d_to_1892 v2 v3)
                  (let v9
                         = coe
                             MAlonzo.Code.Function.Bundles.du_isRightInverse_1904 (coe v0)
                             (coe v1) (coe v2) in
                   coe
                     (let v10
                            = MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v9) in
                      coe
                        (let v11
                               = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v10) in
                         coe
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                              (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v11))
                              (coe MAlonzo.Code.Function.Bundles.d_to_1892 v2 v3) v4 v5)))))
               (coe
                  MAlonzo.Code.Function.Structures.du_strictlyInverse'691'_482
                  (coe MAlonzo.Code.Function.Bundles.d_to_1892 (coe v2))
                  (coe
                     MAlonzo.Code.Function.Bundles.du_isRightInverse_1904 (coe v0)
                     (coe v1) (coe v2))
                  (coe v3)))))
