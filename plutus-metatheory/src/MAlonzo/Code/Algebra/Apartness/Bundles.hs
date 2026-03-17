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

module MAlonzo.Code.Algebra.Apartness.Bundles where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Apartness.Structures
import qualified MAlonzo.Code.Algebra.Bundles
import qualified MAlonzo.Code.Algebra.Consequences.Base
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Algebra.Apartness.Bundles.HeytingCommutativeRing
d_HeytingCommutativeRing_12 a0 a1 a2 = ()
data T_HeytingCommutativeRing_12
  = C_HeytingCommutativeRing'46'constructor_657 (AgdaAny ->
                                                 AgdaAny -> AgdaAny)
                                                (AgdaAny -> AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny)
                                                AgdaAny AgdaAny
                                                MAlonzo.Code.Algebra.Apartness.Structures.T_IsHeytingCommutativeRing_160
-- Algebra.Apartness.Bundles.HeytingCommutativeRing.Carrier
d_Carrier_38 :: T_HeytingCommutativeRing_12 -> ()
d_Carrier_38 = erased
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._≈_
d__'8776'__40 ::
  T_HeytingCommutativeRing_12 -> AgdaAny -> AgdaAny -> ()
d__'8776'__40 = erased
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._#_
d__'35'__42 ::
  T_HeytingCommutativeRing_12 -> AgdaAny -> AgdaAny -> ()
d__'35'__42 = erased
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._+_
d__'43'__44 ::
  T_HeytingCommutativeRing_12 -> AgdaAny -> AgdaAny -> AgdaAny
d__'43'__44 v0
  = case coe v0 of
      C_HeytingCommutativeRing'46'constructor_657 v4 v5 v6 v7 v8 v9
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._*_
d__'42'__46 ::
  T_HeytingCommutativeRing_12 -> AgdaAny -> AgdaAny -> AgdaAny
d__'42'__46 v0
  = case coe v0 of
      C_HeytingCommutativeRing'46'constructor_657 v4 v5 v6 v7 v8 v9
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Apartness.Bundles.HeytingCommutativeRing.-_
d_'45'__48 :: T_HeytingCommutativeRing_12 -> AgdaAny -> AgdaAny
d_'45'__48 v0
  = case coe v0 of
      C_HeytingCommutativeRing'46'constructor_657 v4 v5 v6 v7 v8 v9
        -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Apartness.Bundles.HeytingCommutativeRing.0#
d_0'35'_50 :: T_HeytingCommutativeRing_12 -> AgdaAny
d_0'35'_50 v0
  = case coe v0 of
      C_HeytingCommutativeRing'46'constructor_657 v4 v5 v6 v7 v8 v9
        -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Apartness.Bundles.HeytingCommutativeRing.1#
d_1'35'_52 :: T_HeytingCommutativeRing_12 -> AgdaAny
d_1'35'_52 v0
  = case coe v0 of
      C_HeytingCommutativeRing'46'constructor_657 v4 v5 v6 v7 v8 v9
        -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Apartness.Bundles.HeytingCommutativeRing.isHeytingCommutativeRing
d_isHeytingCommutativeRing_54 ::
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Apartness.Structures.T_IsHeytingCommutativeRing_160
d_isHeytingCommutativeRing_54 v0
  = case coe v0 of
      C_HeytingCommutativeRing'46'constructor_657 v4 v5 v6 v7 v8 v9
        -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._._//_
d__'47''47'__58 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 -> AgdaAny -> AgdaAny -> AgdaAny
d__'47''47'__58 ~v0 ~v1 ~v2 v3 = du__'47''47'__58 v3
du__'47''47'__58 ::
  T_HeytingCommutativeRing_12 -> AgdaAny -> AgdaAny -> AgdaAny
du__'47''47'__58 v0
  = let v1 = d__'43'__44 (coe v0) in
    coe
      (let v2 = d_'45'__48 (coe v0) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du__'47''47'__1096 (coe v1)
            (coe v2)))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._._¬#_
d__'172''35'__60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 -> AgdaAny -> AgdaAny -> ()
d__'172''35'__60 = erased
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.cotrans
d_cotrans_62 ::
  T_HeytingCommutativeRing_12 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_cotrans_62 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_cotrans_736
      (coe
         MAlonzo.Code.Algebra.Apartness.Structures.d_isApartnessRelation_314
         (coe d_isHeytingCommutativeRing_54 (coe v0)))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.irrefl
d_irrefl_64 ::
  T_HeytingCommutativeRing_12 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irrefl_64 = erased
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.sym
d_sym_66 ::
  T_HeytingCommutativeRing_12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_66 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_734
      (coe
         MAlonzo.Code.Algebra.Apartness.Structures.d_isApartnessRelation_314
         (coe d_isHeytingCommutativeRing_54 (coe v0)))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.#⇒invertible
d_'35''8658'invertible_68 ::
  T_HeytingCommutativeRing_12 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'35''8658'invertible_68 v0
  = coe
      MAlonzo.Code.Algebra.Apartness.Structures.d_'35''8658'invertible_454
      (coe d_isHeytingCommutativeRing_54 (coe v0))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.*-assoc
d_'42''45'assoc_70 ::
  T_HeytingCommutativeRing_12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_70 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'assoc_2696
      (coe
         MAlonzo.Code.Algebra.Structures.d_isRing_2832
         (coe
            MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
            (coe d_isHeytingCommutativeRing_54 (coe v0))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.*-comm
d_'42''45'comm_72 ::
  T_HeytingCommutativeRing_12 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'comm_72 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'comm_2834
      (coe
         MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
         (coe d_isHeytingCommutativeRing_54 (coe v0)))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.*-cong
d_'42''45'cong_74 ::
  T_HeytingCommutativeRing_12 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_74 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'cong_2694
      (coe
         MAlonzo.Code.Algebra.Structures.d_isRing_2832
         (coe
            MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
            (coe d_isHeytingCommutativeRing_54 (coe v0))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.∙-congʳ
d_'8729''45'cong'691'_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_76 ~v0 ~v1 ~v2 v3
  = du_'8729''45'cong'691'_76 v3
du_'8729''45'cong'691'_76 ::
  T_HeytingCommutativeRing_12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_76 v0
  = let v1 = d__'43'__44 (coe v0) in
    coe
      (let v2 = d__'42'__46 (coe v0) in
       coe
         (let v3 = d_'45'__48 (coe v0) in
          coe
            (let v4 = d_0'35'_50 (coe v0) in
             coe
               (let v5 = d_isHeytingCommutativeRing_54 (coe v0) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                             (coe v5) in
                   coe
                     (let v7 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v6) in
                      coe
                        (let v8
                               = coe
                                   MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                                   (coe v7) in
                         coe
                           (let v9
                                  = coe
                                      MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2406
                                      (coe v1) (coe v2) (coe v3) (coe v4) (coe v8) in
                            coe
                              (let v10
                                     = coe
                                         MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1280
                                         (coe v9) in
                               coe
                                 (let v11
                                        = coe
                                            MAlonzo.Code.Algebra.Structures.du_setoid_200
                                            (coe v10) in
                                  coe
                                    (let v12
                                           = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                               (coe v10) in
                                     coe
                                       (coe
                                          MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                                          (coe v12)
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                (coe v11)))))))))))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.∙-congˡ
d_'8729''45'cong'737'_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_78 ~v0 ~v1 ~v2 v3
  = du_'8729''45'cong'737'_78 v3
du_'8729''45'cong'737'_78 ::
  T_HeytingCommutativeRing_12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_78 v0
  = let v1 = d__'43'__44 (coe v0) in
    coe
      (let v2 = d__'42'__46 (coe v0) in
       coe
         (let v3 = d_'45'__48 (coe v0) in
          coe
            (let v4 = d_0'35'_50 (coe v0) in
             coe
               (let v5 = d_isHeytingCommutativeRing_54 (coe v0) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                             (coe v5) in
                   coe
                     (let v7 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v6) in
                      coe
                        (let v8
                               = coe
                                   MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                                   (coe v7) in
                         coe
                           (let v9
                                  = coe
                                      MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2406
                                      (coe v1) (coe v2) (coe v3) (coe v4) (coe v8) in
                            coe
                              (let v10
                                     = coe
                                         MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1280
                                         (coe v9) in
                               coe
                                 (let v11
                                        = coe
                                            MAlonzo.Code.Algebra.Structures.du_setoid_200
                                            (coe v10) in
                                  coe
                                    (let v12
                                           = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                               (coe v10) in
                                     coe
                                       (coe
                                          MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                                          (coe v12)
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                (coe v11)))))))))))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.*-identity
d_'42''45'identity_80 ::
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_80 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2698
      (coe
         MAlonzo.Code.Algebra.Structures.d_isRing_2832
         (coe
            MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
            (coe d_isHeytingCommutativeRing_54 (coe v0))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.identityʳ
d_identity'691'_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 -> AgdaAny -> AgdaAny
d_identity'691'_82 ~v0 ~v1 ~v2 v3 = du_identity'691'_82 v3
du_identity'691'_82 ::
  T_HeytingCommutativeRing_12 -> AgdaAny -> AgdaAny
du_identity'691'_82 v0
  = let v1 = d__'43'__44 (coe v0) in
    coe
      (let v2 = d__'42'__46 (coe v0) in
       coe
         (let v3 = d_'45'__48 (coe v0) in
          coe
            (let v4 = d_0'35'_50 (coe v0) in
             coe
               (let v5 = d_isHeytingCommutativeRing_54 (coe v0) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                             (coe v5) in
                   coe
                     (let v7 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v6) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_identity'691'_726
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_2790 (coe v1)
                              (coe v2) (coe v3) (coe v4) (coe v7)))))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.identityˡ
d_identity'737'_84 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 -> AgdaAny -> AgdaAny
d_identity'737'_84 ~v0 ~v1 ~v2 v3 = du_identity'737'_84 v3
du_identity'737'_84 ::
  T_HeytingCommutativeRing_12 -> AgdaAny -> AgdaAny
du_identity'737'_84 v0
  = let v1 = d__'43'__44 (coe v0) in
    coe
      (let v2 = d__'42'__46 (coe v0) in
       coe
         (let v3 = d_'45'__48 (coe v0) in
          coe
            (let v4 = d_0'35'_50 (coe v0) in
             coe
               (let v5 = d_isHeytingCommutativeRing_54 (coe v0) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                             (coe v5) in
                   coe
                     (let v7 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v6) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_identity'737'_724
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_2790 (coe v1)
                              (coe v2) (coe v3) (coe v4) (coe v7)))))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.isCommutativeMagma
d_isCommutativeMagma_86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
d_isCommutativeMagma_86 ~v0 ~v1 ~v2 v3
  = du_isCommutativeMagma_86 v3
du_isCommutativeMagma_86 ::
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
du_isCommutativeMagma_86 v0
  = let v1 = d__'43'__44 (coe v0) in
    coe
      (let v2 = d__'42'__46 (coe v0) in
       coe
         (let v3 = d_'45'__48 (coe v0) in
          coe
            (let v4 = d_0'35'_50 (coe v0) in
             coe
               (let v5 = d_isHeytingCommutativeRing_54 (coe v0) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                             (coe v5) in
                   coe
                     (let v7
                            = coe
                                MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_2946
                                (coe v1) (coe v2) (coe v3) (coe v4) (coe v6) in
                      coe
                        (let v8
                               = coe
                                   MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1798
                                   (coe v7) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_584
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1472
                                 (coe v8))))))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.*-isCommutativeMonoid
d_'42''45'isCommutativeMonoid_88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
d_'42''45'isCommutativeMonoid_88 ~v0 ~v1 ~v2 v3
  = du_'42''45'isCommutativeMonoid_88 v3
du_'42''45'isCommutativeMonoid_88 ::
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
du_'42''45'isCommutativeMonoid_88 v0
  = let v1 = d__'43'__44 (coe v0) in
    coe
      (let v2 = d__'42'__46 (coe v0) in
       coe
         (let v3 = d_'45'__48 (coe v0) in
          coe
            (let v4 = d_0'35'_50 (coe v0) in
             coe
               (let v5 = d_isHeytingCommutativeRing_54 (coe v0) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                             (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeMonoid_1806
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_2946
                           (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
d_'42''45'isCommutativeSemigroup_90 ~v0 ~v1 ~v2 v3
  = du_'42''45'isCommutativeSemigroup_90 v3
du_'42''45'isCommutativeSemigroup_90 ::
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
du_'42''45'isCommutativeSemigroup_90 v0
  = let v1 = d__'43'__44 (coe v0) in
    coe
      (let v2 = d__'42'__46 (coe v0) in
       coe
         (let v3 = d_'45'__48 (coe v0) in
          coe
            (let v4 = d_0'35'_50 (coe v0) in
             coe
               (let v5 = d_isHeytingCommutativeRing_54 (coe v0) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                             (coe v5) in
                   coe
                     (let v7
                            = coe
                                MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_2946
                                (coe v1) (coe v2) (coe v3) (coe v4) (coe v6) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1472
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1798
                              (coe v7)))))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.*-isMagma
d_'42''45'isMagma_92 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'42''45'isMagma_92 ~v0 ~v1 ~v2 v3 = du_'42''45'isMagma_92 v3
du_'42''45'isMagma_92 ::
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_'42''45'isMagma_92 v0
  = let v1 = d__'43'__44 (coe v0) in
    coe
      (let v2 = d__'42'__46 (coe v0) in
       coe
         (let v3 = d_'45'__48 (coe v0) in
          coe
            (let v4 = d_0'35'_50 (coe v0) in
             coe
               (let v5 = d_isHeytingCommutativeRing_54 (coe v0) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                             (coe v5) in
                   coe
                     (let v7 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v6) in
                      coe
                        (let v8
                               = coe
                                   MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                                   (coe v7) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1280
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2406 (coe v1)
                                 (coe v2) (coe v3) (coe v4) (coe v8))))))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.*-isMonoid
d_'42''45'isMonoid_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
d_'42''45'isMonoid_94 ~v0 ~v1 ~v2 v3 = du_'42''45'isMonoid_94 v3
du_'42''45'isMonoid_94 ::
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
du_'42''45'isMonoid_94 v0
  = let v1 = d__'43'__44 (coe v0) in
    coe
      (let v2 = d__'42'__46 (coe v0) in
       coe
         (let v3 = d_'45'__48 (coe v0) in
          coe
            (let v4 = d_0'35'_50 (coe v0) in
             coe
               (let v5 = d_isHeytingCommutativeRing_54 (coe v0) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                             (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_2790 (coe v1)
                        (coe v2) (coe v3) (coe v4)
                        (coe MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v6))))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.*-isSemigroup
d_'42''45'isSemigroup_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_'42''45'isSemigroup_96 ~v0 ~v1 ~v2 v3
  = du_'42''45'isSemigroup_96 v3
du_'42''45'isSemigroup_96 ::
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
du_'42''45'isSemigroup_96 v0
  = let v1 = d__'43'__44 (coe v0) in
    coe
      (let v2 = d__'42'__46 (coe v0) in
       coe
         (let v3 = d_'45'__48 (coe v0) in
          coe
            (let v4 = d_0'35'_50 (coe v0) in
             coe
               (let v5 = d_isHeytingCommutativeRing_54 (coe v0) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                             (coe v5) in
                   coe
                     (let v7 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v6) in
                      coe
                        (let v8
                               = coe
                                   MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                                   (coe v7) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1282
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2406 (coe v1)
                                 (coe v2) (coe v3) (coe v4) (coe v8))))))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.assoc
d_assoc_98 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_98 ~v0 ~v1 ~v2 v3 = du_assoc_98 v3
du_assoc_98 ::
  T_HeytingCommutativeRing_12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_assoc_98 v0
  = let v1 = d_isHeytingCommutativeRing_54 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.d_assoc_480
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                           (coe v3))))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.comm
d_comm_100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_100 ~v0 ~v1 ~v2 v3 = du_comm_100 v3
du_comm_100 ::
  T_HeytingCommutativeRing_12 -> AgdaAny -> AgdaAny -> AgdaAny
du_comm_100 v0
  = let v1 = d_isHeytingCommutativeRing_54 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.d_comm_1144
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                  (coe v3)))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.∙-cong
d_'8729''45'cong_102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_102 ~v0 ~v1 ~v2 v3 = du_'8729''45'cong_102 v3
du_'8729''45'cong_102 ::
  T_HeytingCommutativeRing_12 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong_102 v0
  = let v1 = d_isHeytingCommutativeRing_54 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMagma_478
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                              (coe v3)))))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.∙-congʳ
d_'8729''45'cong'691'_104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_104 ~v0 ~v1 ~v2 v3
  = du_'8729''45'cong'691'_104 v3
du_'8729''45'cong'691'_104 ::
  T_HeytingCommutativeRing_12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_104 v0
  = let v1 = d_isHeytingCommutativeRing_54 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v6) in
                      coe
                        (let v8
                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v7) in
                         coe
                           (let v9 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v8) in
                            coe
                              (let v10
                                     = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v9) in
                               coe
                                 (let v11
                                        = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                            (coe v9) in
                                  coe
                                    (coe
                                       MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                                       (coe v11)
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                             (coe v10))))))))))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.∙-congˡ
d_'8729''45'cong'737'_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_106 ~v0 ~v1 ~v2 v3
  = du_'8729''45'cong'737'_106 v3
du_'8729''45'cong'737'_106 ::
  T_HeytingCommutativeRing_12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_106 v0
  = let v1 = d_isHeytingCommutativeRing_54 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v6) in
                      coe
                        (let v8
                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v7) in
                         coe
                           (let v9 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v8) in
                            coe
                              (let v10
                                     = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v9) in
                               coe
                                 (let v11
                                        = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                            (coe v9) in
                                  coe
                                    (coe
                                       MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                                       (coe v11)
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                             (coe v10))))))))))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.identity
d_identity_108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_108 ~v0 ~v1 ~v2 v3 = du_identity_108 v3
du_identity_108 ::
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_identity_108 v0
  = let v1 = d_isHeytingCommutativeRing_54 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.d_identity_696
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                        (coe v3)))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.identityʳ
d_identity'691'_110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 -> AgdaAny -> AgdaAny
d_identity'691'_110 ~v0 ~v1 ~v2 v3 = du_identity'691'_110 v3
du_identity'691'_110 ::
  T_HeytingCommutativeRing_12 -> AgdaAny -> AgdaAny
du_identity'691'_110 v0
  = let v1 = d_isHeytingCommutativeRing_54 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_identity'691'_726
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v6))))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.identityˡ
d_identity'737'_112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 -> AgdaAny -> AgdaAny
d_identity'737'_112 ~v0 ~v1 ~v2 v3 = du_identity'737'_112 v3
du_identity'737'_112 ::
  T_HeytingCommutativeRing_12 -> AgdaAny -> AgdaAny
du_identity'737'_112 v0
  = let v1 = d_isHeytingCommutativeRing_54 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_identity'737'_724
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v6))))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.+-isAbelianGroup
d_'43''45'isAbelianGroup_114 ::
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1130
d_'43''45'isAbelianGroup_114 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
      (coe
         MAlonzo.Code.Algebra.Structures.d_isRing_2832
         (coe
            MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
            (coe d_isHeytingCommutativeRing_54 (coe v0))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.isCommutativeMagma
d_isCommutativeMagma_116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
d_isCommutativeMagma_116 ~v0 ~v1 ~v2 v3
  = du_isCommutativeMagma_116 v3
du_isCommutativeMagma_116 ::
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
du_isCommutativeMagma_116 v0
  = let v1 = d_isHeytingCommutativeRing_54 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                          (coe v4) in
                coe
                  (let v6
                         = coe
                             MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1202
                             (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_584
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_784
                           (coe v6))))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.isCommutativeMonoid
d_isCommutativeMonoid_118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
d_isCommutativeMonoid_118 ~v0 ~v1 ~v2 v3
  = du_isCommutativeMonoid_118 v3
du_isCommutativeMonoid_118 ::
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
du_isCommutativeMonoid_118 v0
  = let v1 = d_isHeytingCommutativeRing_54 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1202
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                     (coe v4))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.isCommutativeSemigroup
d_isCommutativeSemigroup_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
d_isCommutativeSemigroup_120 ~v0 ~v1 ~v2 v3
  = du_isCommutativeSemigroup_120 v3
du_isCommutativeSemigroup_120 ::
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
du_isCommutativeSemigroup_120 v0
  = let v1 = d_isHeytingCommutativeRing_54 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_784
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1202
                        (coe v5)))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.isGroup
d_isGroup_122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1034
d_isGroup_122 ~v0 ~v1 ~v2 v3 = du_isGroup_122 v3
du_isGroup_122 ::
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1034
du_isGroup_122 v0
  = let v1 = d_isHeytingCommutativeRing_54 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.d_isGroup_1142
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                  (coe v3)))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.isInvertibleMagma
d_isInvertibleMagma_124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_922
d_isInvertibleMagma_124 ~v0 ~v1 ~v2 v3
  = du_isInvertibleMagma_124 v3
du_isInvertibleMagma_124 ::
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_922
du_isInvertibleMagma_124 v0
  = let v1 = d_isHeytingCommutativeRing_54 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_isInvertibleMagma_1120
                     (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v5)))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_974
d_isInvertibleUnitalMagma_126 ~v0 ~v1 ~v2 v3
  = du_isInvertibleUnitalMagma_126 v3
du_isInvertibleUnitalMagma_126 ::
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_974
du_isInvertibleUnitalMagma_126 v0
  = let v1 = d_isHeytingCommutativeRing_54 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_isInvertibleUnitalMagma_1122
                     (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v5)))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.isMagma
d_isMagma_128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_128 ~v0 ~v1 ~v2 v3 = du_isMagma_128 v3
du_isMagma_128 ::
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_isMagma_128 v0
  = let v1 = d_isHeytingCommutativeRing_54 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_478
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                           (coe v3))))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.isMonoid
d_isMonoid_130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
d_isMonoid_130 ~v0 ~v1 ~v2 v3 = du_isMonoid_130 v3
du_isMonoid_130 ::
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
du_isMonoid_130 v0
  = let v1 = d_isHeytingCommutativeRing_54 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                     (coe v3))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.isSemigroup
d_isSemigroup_132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_isSemigroup_132 ~v0 ~v1 ~v2 v3 = du_isSemigroup_132 v3
du_isSemigroup_132 ::
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
du_isSemigroup_132 v0
  = let v1 = d_isHeytingCommutativeRing_54 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                        (coe v3)))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.isUnitalMagma
d_isUnitalMagma_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_640
d_isUnitalMagma_134 ~v0 ~v1 ~v2 v3 = du_isUnitalMagma_134 v3
du_isUnitalMagma_134 ::
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_640
du_isUnitalMagma_134 v0
  = let v1 = d_isHeytingCommutativeRing_54 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_728
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v6))))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.⁻¹-cong
d_'8315''185''45'cong_136 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'cong_136 ~v0 ~v1 ~v2 v3
  = du_'8315''185''45'cong_136 v3
du_'8315''185''45'cong_136 ::
  T_HeytingCommutativeRing_12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8315''185''45'cong_136 v0
  = let v1 = d_isHeytingCommutativeRing_54 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.d_'8315''185''45'cong_1052
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                     (coe v3))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.inverse
d_inverse_138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_138 ~v0 ~v1 ~v2 v3 = du_inverse_138 v3
du_inverse_138 ::
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inverse_138 v0
  = let v1 = d_isHeytingCommutativeRing_54 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.d_inverse_1050
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                     (coe v3))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.inverseʳ
d_inverse'691'_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 -> AgdaAny -> AgdaAny
d_inverse'691'_140 ~v0 ~v1 ~v2 v3 = du_inverse'691'_140 v3
du_inverse'691'_140 ::
  T_HeytingCommutativeRing_12 -> AgdaAny -> AgdaAny
du_inverse'691'_140 v0
  = let v1 = d_isHeytingCommutativeRing_54 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_inverse'691'_1106
                     (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v5)))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.inverseˡ
d_inverse'737'_142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 -> AgdaAny -> AgdaAny
d_inverse'737'_142 ~v0 ~v1 ~v2 v3 = du_inverse'737'_142 v3
du_inverse'737'_142 ::
  T_HeytingCommutativeRing_12 -> AgdaAny -> AgdaAny
du_inverse'737'_142 v0
  = let v1 = d_isHeytingCommutativeRing_54 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_inverse'737'_1104
                     (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v5)))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.distrib
d_distrib_144 ::
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_144 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_2700
      (coe
         MAlonzo.Code.Algebra.Structures.d_isRing_2832
         (coe
            MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
            (coe d_isHeytingCommutativeRing_54 (coe v0))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.distribʳ
d_distrib'691'_146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_146 ~v0 ~v1 ~v2 v3 = du_distrib'691'_146 v3
du_distrib'691'_146 ::
  T_HeytingCommutativeRing_12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'691'_146 v0
  = let v1 = d_isHeytingCommutativeRing_54 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_distrib'691'_2398
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                  (coe v3)))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.distribˡ
d_distrib'737'_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_148 ~v0 ~v1 ~v2 v3 = du_distrib'737'_148 v3
du_distrib'737'_148 ::
  T_HeytingCommutativeRing_12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'737'_148 v0
  = let v1 = d_isHeytingCommutativeRing_54 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_distrib'737'_2396
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                  (coe v3)))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.invertible⇒#
d_invertible'8658''35'_150 ::
  T_HeytingCommutativeRing_12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_invertible'8658''35'_150 v0
  = coe
      MAlonzo.Code.Algebra.Apartness.Structures.d_invertible'8658''35'_460
      (coe d_isHeytingCommutativeRing_54 (coe v0))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.isApartnessRelation
d_isApartnessRelation_152 ::
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722
d_isApartnessRelation_152 v0
  = coe
      MAlonzo.Code.Algebra.Apartness.Structures.d_isApartnessRelation_314
      (coe d_isHeytingCommutativeRing_54 (coe v0))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.isCommutativeRing
d_isCommutativeRing_154 ::
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816
d_isCommutativeRing_154 v0
  = coe
      MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
      (coe d_isHeytingCommutativeRing_54 (coe v0))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.isCommutativeSemiring
d_isCommutativeSemiring_156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1696
d_isCommutativeSemiring_156 ~v0 ~v1 ~v2 v3
  = du_isCommutativeSemiring_156 v3
du_isCommutativeSemiring_156 ::
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1696
du_isCommutativeSemiring_156 v0
  = let v1 = d__'43'__44 (coe v0) in
    coe
      (let v2 = d__'42'__46 (coe v0) in
       coe
         (let v3 = d_'45'__48 (coe v0) in
          coe
            (let v4 = d_0'35'_50 (coe v0) in
             coe
               (let v5 = d_isHeytingCommutativeRing_54 (coe v0) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_2946
                     (coe v1) (coe v2) (coe v3) (coe v4)
                     (coe
                        MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                        (coe v5)))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.isCommutativeSemiringWithoutOne
d_isCommutativeSemiringWithoutOne_158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1390
d_isCommutativeSemiringWithoutOne_158 ~v0 ~v1 ~v2 v3
  = du_isCommutativeSemiringWithoutOne_158 v3
du_isCommutativeSemiringWithoutOne_158 ::
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1390
du_isCommutativeSemiringWithoutOne_158 v0
  = let v1 = d__'43'__44 (coe v0) in
    coe
      (let v2 = d__'42'__46 (coe v0) in
       coe
         (let v3 = d_'45'__48 (coe v0) in
          coe
            (let v4 = d_0'35'_50 (coe v0) in
             coe
               (let v5 = d_isHeytingCommutativeRing_54 (coe v0) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                             (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1798
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_2946
                           (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.isEquivalence
d_isEquivalence_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_160 ~v0 ~v1 ~v2 v3 = du_isEquivalence_160 v3
du_isEquivalence_160 ::
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_160 v0
  = let v1 = d_isHeytingCommutativeRing_54 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMagma_478
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                              (coe v3)))))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.isNearSemiring
d_isNearSemiring_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1216
d_isNearSemiring_162 ~v0 ~v1 ~v2 v3 = du_isNearSemiring_162 v3
du_isNearSemiring_162 ::
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1216
du_isNearSemiring_162 v0
  = let v1 = d__'43'__44 (coe v0) in
    coe
      (let v2 = d__'42'__46 (coe v0) in
       coe
         (let v3 = d_'45'__48 (coe v0) in
          coe
            (let v4 = d_0'35'_50 (coe v0) in
             coe
               (let v5 = d_isHeytingCommutativeRing_54 (coe v0) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                             (coe v5) in
                   coe
                     (let v7 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v6) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2406 (coe v1)
                           (coe v2) (coe v3) (coe v4)
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                              (coe v7)))))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.isPartialEquivalence
d_isPartialEquivalence_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_164 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_164 v3
du_isPartialEquivalence_164 ::
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_164 v0
  = let v1 = d_isHeytingCommutativeRing_54 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v6) in
                      coe
                        (let v8
                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v7) in
                         coe
                           (let v9 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v8) in
                            coe
                              (coe
                                 MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                    (coe v9)))))))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.isRing
d_isRing_166 ::
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2670
d_isRing_166 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isRing_2832
      (coe
         MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
         (coe d_isHeytingCommutativeRing_54 (coe v0)))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.isRingWithoutOne
d_isRingWithoutOne_168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2304
d_isRingWithoutOne_168 ~v0 ~v1 ~v2 v3 = du_isRingWithoutOne_168 v3
du_isRingWithoutOne_168 ::
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2304
du_isRingWithoutOne_168 v0
  = let v1 = d_isHeytingCommutativeRing_54 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
            (coe MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.isSemiring
d_isSemiring_170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1588
d_isSemiring_170 ~v0 ~v1 ~v2 v3 = du_isSemiring_170 v3
du_isSemiring_170 ::
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1588
du_isSemiring_170 v0
  = let v1 = d__'43'__44 (coe v0) in
    coe
      (let v2 = d__'42'__46 (coe v0) in
       coe
         (let v3 = d_'45'__48 (coe v0) in
          coe
            (let v4 = d_0'35'_50 (coe v0) in
             coe
               (let v5 = d_isHeytingCommutativeRing_54 (coe v0) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                             (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_isSemiring_2800 (coe v1)
                        (coe v2) (coe v3) (coe v4)
                        (coe MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v6))))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1486
d_isSemiringWithoutAnnihilatingZero_172 ~v0 ~v1 ~v2 v3
  = du_isSemiringWithoutAnnihilatingZero_172 v3
du_isSemiringWithoutAnnihilatingZero_172 ::
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1486
du_isSemiringWithoutAnnihilatingZero_172 v0
  = let v1 = d_isHeytingCommutativeRing_54 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutAnnihilatingZero_2798
            (coe MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.isSemiringWithoutOne
d_isSemiringWithoutOne_174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1296
d_isSemiringWithoutOne_174 ~v0 ~v1 ~v2 v3
  = du_isSemiringWithoutOne_174 v3
du_isSemiringWithoutOne_174 ::
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1296
du_isSemiringWithoutOne_174 v0
  = let v1 = d__'43'__44 (coe v0) in
    coe
      (let v2 = d__'42'__46 (coe v0) in
       coe
         (let v3 = d_'45'__48 (coe v0) in
          coe
            (let v4 = d_0'35'_50 (coe v0) in
             coe
               (let v5 = d_isHeytingCommutativeRing_54 (coe v0) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                             (coe v5) in
                   coe
                     (let v7 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v6) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1678
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_isSemiring_2800 (coe v1)
                              (coe v2) (coe v3) (coe v4) (coe v7)))))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.refl
d_refl_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 -> AgdaAny -> AgdaAny
d_refl_176 ~v0 ~v1 ~v2 v3 = du_refl_176 v3
du_refl_176 :: T_HeytingCommutativeRing_12 -> AgdaAny -> AgdaAny
du_refl_176 v0
  = let v1 = d_isHeytingCommutativeRing_54 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_refl_34
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isMagma_478
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                                 (coe v3))))))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.reflexive
d_reflexive_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_178 ~v0 ~v1 ~v2 v3 = du_reflexive_178 v3
du_reflexive_178 ::
  T_HeytingCommutativeRing_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_178 v0
  = let v1 = d_isHeytingCommutativeRing_54 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v6) in
                      coe
                        (let v8
                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v7) in
                         coe
                           (let v9 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v8) in
                            coe
                              (\ v10 v11 v12 ->
                                 coe
                                   MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                                   (coe
                                      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v9))
                                   v10)))))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.setoid
d_setoid_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_180 ~v0 ~v1 ~v2 v3 = du_setoid_180 v3
du_setoid_180 ::
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_180 v0
  = let v1 = d_isHeytingCommutativeRing_54 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v6) in
                      coe
                        (let v8
                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v7) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_setoid_200
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v8))))))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.sym
d_sym_182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_182 ~v0 ~v1 ~v2 v3 = du_sym_182 v3
du_sym_182 ::
  T_HeytingCommutativeRing_12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_182 v0
  = let v1 = d_isHeytingCommutativeRing_54 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isMagma_478
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                                 (coe v3))))))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.trans
d_trans_184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_184 ~v0 ~v1 ~v2 v3 = du_trans_184 v3
du_trans_184 ::
  T_HeytingCommutativeRing_12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_184 v0
  = let v1 = d_isHeytingCommutativeRing_54 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isMagma_478
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                                 (coe v3))))))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'691''45''8315''185'_186 ~v0 ~v1 ~v2 v3
  = du_unique'691''45''8315''185'_186 v3
du_unique'691''45''8315''185'_186 ::
  T_HeytingCommutativeRing_12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'691''45''8315''185'_186 v0
  = let v1 = d__'43'__44 (coe v0) in
    coe
      (let v2 = d_'45'__48 (coe v0) in
       coe
         (let v3 = d_0'35'_50 (coe v0) in
          coe
            (let v4 = d_isHeytingCommutativeRing_54 (coe v0) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                          (coe v4) in
                coe
                  (let v6 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v5) in
                   coe
                     (let v7
                            = coe
                                MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                                (coe v6) in
                      coe
                        (let v8
                               = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                   (coe v7) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_unique'691''45''8315''185'_1118
                              (coe v1) (coe v3) (coe v2)
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v8))))))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'737''45''8315''185'_188 ~v0 ~v1 ~v2 v3
  = du_unique'737''45''8315''185'_188 v3
du_unique'737''45''8315''185'_188 ::
  T_HeytingCommutativeRing_12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'737''45''8315''185'_188 v0
  = let v1 = d__'43'__44 (coe v0) in
    coe
      (let v2 = d_'45'__48 (coe v0) in
       coe
         (let v3 = d_0'35'_50 (coe v0) in
          coe
            (let v4 = d_isHeytingCommutativeRing_54 (coe v0) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                          (coe v4) in
                coe
                  (let v6 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v5) in
                   coe
                     (let v7
                            = coe
                                MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                                (coe v6) in
                      coe
                        (let v8
                               = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                   (coe v7) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_unique'737''45''8315''185'_1112
                              (coe v1) (coe v3) (coe v2)
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v8))))))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.zero
d_zero_190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_190 ~v0 ~v1 ~v2 v3 = du_zero_190 v3
du_zero_190 ::
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_zero_190 v0
  = let v1 = d__'43'__44 (coe v0) in
    coe
      (let v2 = d__'42'__46 (coe v0) in
       coe
         (let v3 = d_'45'__48 (coe v0) in
          coe
            (let v4 = d_0'35'_50 (coe v0) in
             coe
               (let v5 = d_isHeytingCommutativeRing_54 (coe v0) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                             (coe v5) in
                   coe
                     (let v7 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v6) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_zero_2404 (coe v1) (coe v2)
                           (coe v3) (coe v4)
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                              (coe v7)))))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.zeroʳ
d_zero'691'_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 -> AgdaAny -> AgdaAny
d_zero'691'_192 ~v0 ~v1 ~v2 v3 = du_zero'691'_192 v3
du_zero'691'_192 ::
  T_HeytingCommutativeRing_12 -> AgdaAny -> AgdaAny
du_zero'691'_192 v0
  = let v1 = d__'43'__44 (coe v0) in
    coe
      (let v2 = d__'42'__46 (coe v0) in
       coe
         (let v3 = d_'45'__48 (coe v0) in
          coe
            (let v4 = d_0'35'_50 (coe v0) in
             coe
               (let v5 = d_isHeytingCommutativeRing_54 (coe v0) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                             (coe v5) in
                   coe
                     (let v7 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v6) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_zero'691'_2402 (coe v1) (coe v2)
                           (coe v3) (coe v4)
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                              (coe v7)))))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.zeroˡ
d_zero'737'_194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 -> AgdaAny -> AgdaAny
d_zero'737'_194 ~v0 ~v1 ~v2 v3 = du_zero'737'_194 v3
du_zero'737'_194 ::
  T_HeytingCommutativeRing_12 -> AgdaAny -> AgdaAny
du_zero'737'_194 v0
  = let v1 = d__'43'__44 (coe v0) in
    coe
      (let v2 = d__'42'__46 (coe v0) in
       coe
         (let v3 = d_'45'__48 (coe v0) in
          coe
            (let v4 = d_0'35'_50 (coe v0) in
             coe
               (let v5 = d_isHeytingCommutativeRing_54 (coe v0) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                             (coe v5) in
                   coe
                     (let v7 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v6) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_zero'737'_2400 (coe v1) (coe v2)
                           (coe v3) (coe v4)
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                              (coe v7)))))))))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing._.¬#-isEquivalence
d_'172''35''45'isEquivalence_196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_'172''35''45'isEquivalence_196 ~v0 ~v1 ~v2 ~v3
  = du_'172''35''45'isEquivalence_196
du_'172''35''45'isEquivalence_196 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_'172''35''45'isEquivalence_196
  = coe
      MAlonzo.Code.Algebra.Apartness.Structures.du_'172''35''45'isEquivalence_462
-- Algebra.Apartness.Bundles.HeytingCommutativeRing.commutativeRing
d_commutativeRing_198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeRing_4054
d_commutativeRing_198 ~v0 ~v1 ~v2 v3 = du_commutativeRing_198 v3
du_commutativeRing_198 ::
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeRing_4054
du_commutativeRing_198 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeRing'46'constructor_73489
      (d__'43'__44 (coe v0)) (d__'42'__46 (coe v0)) (d_'45'__48 (coe v0))
      (d_0'35'_50 (coe v0)) (d_1'35'_52 (coe v0))
      (MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
         (coe d_isHeytingCommutativeRing_54 (coe v0)))
-- Algebra.Apartness.Bundles.HeytingCommutativeRing.apartnessRelation
d_apartnessRelation_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_ApartnessRelation_1484
d_apartnessRelation_200 ~v0 ~v1 ~v2 v3
  = du_apartnessRelation_200 v3
du_apartnessRelation_200 ::
  T_HeytingCommutativeRing_12 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_ApartnessRelation_1484
du_apartnessRelation_200 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_ApartnessRelation'46'constructor_28831
      (MAlonzo.Code.Algebra.Apartness.Structures.d_isApartnessRelation_314
         (coe d_isHeytingCommutativeRing_54 (coe v0)))
-- Algebra.Apartness.Bundles.HeytingField
d_HeytingField_208 a0 a1 a2 = ()
data T_HeytingField_208
  = C_HeytingField'46'constructor_4995 (AgdaAny ->
                                        AgdaAny -> AgdaAny)
                                       (AgdaAny -> AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny) AgdaAny
                                       AgdaAny
                                       MAlonzo.Code.Algebra.Apartness.Structures.T_IsHeytingField_464
-- Algebra.Apartness.Bundles.HeytingField.Carrier
d_Carrier_234 :: T_HeytingField_208 -> ()
d_Carrier_234 = erased
-- Algebra.Apartness.Bundles.HeytingField._≈_
d__'8776'__236 :: T_HeytingField_208 -> AgdaAny -> AgdaAny -> ()
d__'8776'__236 = erased
-- Algebra.Apartness.Bundles.HeytingField._#_
d__'35'__238 :: T_HeytingField_208 -> AgdaAny -> AgdaAny -> ()
d__'35'__238 = erased
-- Algebra.Apartness.Bundles.HeytingField._+_
d__'43'__240 :: T_HeytingField_208 -> AgdaAny -> AgdaAny -> AgdaAny
d__'43'__240 v0
  = case coe v0 of
      C_HeytingField'46'constructor_4995 v4 v5 v6 v7 v8 v9 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Apartness.Bundles.HeytingField._*_
d__'42'__242 :: T_HeytingField_208 -> AgdaAny -> AgdaAny -> AgdaAny
d__'42'__242 v0
  = case coe v0 of
      C_HeytingField'46'constructor_4995 v4 v5 v6 v7 v8 v9 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Apartness.Bundles.HeytingField.-_
d_'45'__244 :: T_HeytingField_208 -> AgdaAny -> AgdaAny
d_'45'__244 v0
  = case coe v0 of
      C_HeytingField'46'constructor_4995 v4 v5 v6 v7 v8 v9 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Apartness.Bundles.HeytingField.0#
d_0'35'_246 :: T_HeytingField_208 -> AgdaAny
d_0'35'_246 v0
  = case coe v0 of
      C_HeytingField'46'constructor_4995 v4 v5 v6 v7 v8 v9 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Apartness.Bundles.HeytingField.1#
d_1'35'_248 :: T_HeytingField_208 -> AgdaAny
d_1'35'_248 v0
  = case coe v0 of
      C_HeytingField'46'constructor_4995 v4 v5 v6 v7 v8 v9 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Apartness.Bundles.HeytingField.isHeytingField
d_isHeytingField_250 ::
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Apartness.Structures.T_IsHeytingField_464
d_isHeytingField_250 v0
  = case coe v0 of
      C_HeytingField'46'constructor_4995 v4 v5 v6 v7 v8 v9 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Apartness.Bundles.HeytingField._._//_
d__'47''47'__254 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 -> AgdaAny -> AgdaAny -> AgdaAny
d__'47''47'__254 ~v0 ~v1 ~v2 v3 = du__'47''47'__254 v3
du__'47''47'__254 ::
  T_HeytingField_208 -> AgdaAny -> AgdaAny -> AgdaAny
du__'47''47'__254 v0
  = let v1 = d__'43'__240 (coe v0) in
    coe
      (let v2 = d_'45'__244 (coe v0) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du__'47''47'__1096 (coe v1)
            (coe v2)))
-- Algebra.Apartness.Bundles.HeytingField._._¬#_
d__'172''35'__256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 -> AgdaAny -> AgdaAny -> ()
d__'172''35'__256 = erased
-- Algebra.Apartness.Bundles.HeytingField._.cotrans
d_cotrans_258 ::
  T_HeytingField_208 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_cotrans_258 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_cotrans_736
      (coe
         MAlonzo.Code.Algebra.Apartness.Structures.d_isApartnessRelation_314
         (coe
            MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
            (coe d_isHeytingField_250 (coe v0))))
-- Algebra.Apartness.Bundles.HeytingField._.irrefl
d_irrefl_260 ::
  T_HeytingField_208 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irrefl_260 = erased
-- Algebra.Apartness.Bundles.HeytingField._.sym
d_sym_262 ::
  T_HeytingField_208 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_262 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_734
      (coe
         MAlonzo.Code.Algebra.Apartness.Structures.d_isApartnessRelation_314
         (coe
            MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
            (coe d_isHeytingField_250 (coe v0))))
-- Algebra.Apartness.Bundles.HeytingField._.#⇒invertible
d_'35''8658'invertible_264 ::
  T_HeytingField_208 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'35''8658'invertible_264 v0
  = coe
      MAlonzo.Code.Algebra.Apartness.Structures.d_'35''8658'invertible_454
      (coe
         MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
         (coe d_isHeytingField_250 (coe v0)))
-- Algebra.Apartness.Bundles.HeytingField._.*-assoc
d_'42''45'assoc_266 ::
  T_HeytingField_208 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_266 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'assoc_2696
      (coe
         MAlonzo.Code.Algebra.Structures.d_isRing_2832
         (coe
            MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
            (coe
               MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
               (coe d_isHeytingField_250 (coe v0)))))
-- Algebra.Apartness.Bundles.HeytingField._.*-comm
d_'42''45'comm_268 ::
  T_HeytingField_208 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'comm_268 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'comm_2834
      (coe
         MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
         (coe
            MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
            (coe d_isHeytingField_250 (coe v0))))
-- Algebra.Apartness.Bundles.HeytingField._.*-cong
d_'42''45'cong_270 ::
  T_HeytingField_208 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_270 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'cong_2694
      (coe
         MAlonzo.Code.Algebra.Structures.d_isRing_2832
         (coe
            MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
            (coe
               MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
               (coe d_isHeytingField_250 (coe v0)))))
-- Algebra.Apartness.Bundles.HeytingField._.∙-congʳ
d_'8729''45'cong'691'_272 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_272 ~v0 ~v1 ~v2 v3
  = du_'8729''45'cong'691'_272 v3
du_'8729''45'cong'691'_272 ::
  T_HeytingField_208 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_272 v0
  = let v1 = d__'43'__240 (coe v0) in
    coe
      (let v2 = d__'42'__242 (coe v0) in
       coe
         (let v3 = d_'45'__244 (coe v0) in
          coe
            (let v4 = d_0'35'_246 (coe v0) in
             coe
               (let v5 = d_isHeytingField_250 (coe v0) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                             (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                                (coe v6) in
                      coe
                        (let v8 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v7) in
                         coe
                           (let v9
                                  = coe
                                      MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                                      (coe v8) in
                            coe
                              (let v10
                                     = coe
                                         MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2406
                                         (coe v1) (coe v2) (coe v3) (coe v4) (coe v9) in
                               coe
                                 (let v11
                                        = coe
                                            MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1280
                                            (coe v10) in
                                  coe
                                    (let v12
                                           = coe
                                               MAlonzo.Code.Algebra.Structures.du_setoid_200
                                               (coe v11) in
                                     coe
                                       (let v13
                                              = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                                  (coe v11) in
                                        coe
                                          (coe
                                             MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                                             (coe v13)
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                                (coe
                                                   MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                   (coe v12))))))))))))))))
-- Algebra.Apartness.Bundles.HeytingField._.∙-congˡ
d_'8729''45'cong'737'_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_274 ~v0 ~v1 ~v2 v3
  = du_'8729''45'cong'737'_274 v3
du_'8729''45'cong'737'_274 ::
  T_HeytingField_208 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_274 v0
  = let v1 = d__'43'__240 (coe v0) in
    coe
      (let v2 = d__'42'__242 (coe v0) in
       coe
         (let v3 = d_'45'__244 (coe v0) in
          coe
            (let v4 = d_0'35'_246 (coe v0) in
             coe
               (let v5 = d_isHeytingField_250 (coe v0) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                             (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                                (coe v6) in
                      coe
                        (let v8 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v7) in
                         coe
                           (let v9
                                  = coe
                                      MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                                      (coe v8) in
                            coe
                              (let v10
                                     = coe
                                         MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2406
                                         (coe v1) (coe v2) (coe v3) (coe v4) (coe v9) in
                               coe
                                 (let v11
                                        = coe
                                            MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1280
                                            (coe v10) in
                                  coe
                                    (let v12
                                           = coe
                                               MAlonzo.Code.Algebra.Structures.du_setoid_200
                                               (coe v11) in
                                     coe
                                       (let v13
                                              = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                                  (coe v11) in
                                        coe
                                          (coe
                                             MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                                             (coe v13)
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                                (coe
                                                   MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                   (coe v12))))))))))))))))
-- Algebra.Apartness.Bundles.HeytingField._.*-identity
d_'42''45'identity_276 ::
  T_HeytingField_208 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_276 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2698
      (coe
         MAlonzo.Code.Algebra.Structures.d_isRing_2832
         (coe
            MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
            (coe
               MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
               (coe d_isHeytingField_250 (coe v0)))))
-- Algebra.Apartness.Bundles.HeytingField._.identityʳ
d_identity'691'_278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 -> AgdaAny -> AgdaAny
d_identity'691'_278 ~v0 ~v1 ~v2 v3 = du_identity'691'_278 v3
du_identity'691'_278 :: T_HeytingField_208 -> AgdaAny -> AgdaAny
du_identity'691'_278 v0
  = let v1 = d__'43'__240 (coe v0) in
    coe
      (let v2 = d__'42'__242 (coe v0) in
       coe
         (let v3 = d_'45'__244 (coe v0) in
          coe
            (let v4 = d_0'35'_246 (coe v0) in
             coe
               (let v5 = d_isHeytingField_250 (coe v0) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                             (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                                (coe v6) in
                      coe
                        (let v8 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v7) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_identity'691'_726
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_2790 (coe v1)
                                 (coe v2) (coe v3) (coe v4) (coe v8))))))))))
-- Algebra.Apartness.Bundles.HeytingField._.identityˡ
d_identity'737'_280 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 -> AgdaAny -> AgdaAny
d_identity'737'_280 ~v0 ~v1 ~v2 v3 = du_identity'737'_280 v3
du_identity'737'_280 :: T_HeytingField_208 -> AgdaAny -> AgdaAny
du_identity'737'_280 v0
  = let v1 = d__'43'__240 (coe v0) in
    coe
      (let v2 = d__'42'__242 (coe v0) in
       coe
         (let v3 = d_'45'__244 (coe v0) in
          coe
            (let v4 = d_0'35'_246 (coe v0) in
             coe
               (let v5 = d_isHeytingField_250 (coe v0) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                             (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                                (coe v6) in
                      coe
                        (let v8 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v7) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_identity'737'_724
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_2790 (coe v1)
                                 (coe v2) (coe v3) (coe v4) (coe v8))))))))))
-- Algebra.Apartness.Bundles.HeytingField._.isCommutativeMagma
d_isCommutativeMagma_282 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
d_isCommutativeMagma_282 ~v0 ~v1 ~v2 v3
  = du_isCommutativeMagma_282 v3
du_isCommutativeMagma_282 ::
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
du_isCommutativeMagma_282 v0
  = let v1 = d__'43'__240 (coe v0) in
    coe
      (let v2 = d__'42'__242 (coe v0) in
       coe
         (let v3 = d_'45'__244 (coe v0) in
          coe
            (let v4 = d_0'35'_246 (coe v0) in
             coe
               (let v5 = d_isHeytingField_250 (coe v0) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                             (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                                (coe v6) in
                      coe
                        (let v8
                               = coe
                                   MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_2946
                                   (coe v1) (coe v2) (coe v3) (coe v4) (coe v7) in
                         coe
                           (let v9
                                  = coe
                                      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1798
                                      (coe v8) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_584
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1472
                                    (coe v9)))))))))))
-- Algebra.Apartness.Bundles.HeytingField._.*-isCommutativeMonoid
d_'42''45'isCommutativeMonoid_284 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
d_'42''45'isCommutativeMonoid_284 ~v0 ~v1 ~v2 v3
  = du_'42''45'isCommutativeMonoid_284 v3
du_'42''45'isCommutativeMonoid_284 ::
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
du_'42''45'isCommutativeMonoid_284 v0
  = let v1 = d__'43'__240 (coe v0) in
    coe
      (let v2 = d__'42'__242 (coe v0) in
       coe
         (let v3 = d_'45'__244 (coe v0) in
          coe
            (let v4 = d_0'35'_246 (coe v0) in
             coe
               (let v5 = d_isHeytingField_250 (coe v0) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                             (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                                (coe v6) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeMonoid_1806
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_2946
                              (coe v1) (coe v2) (coe v3) (coe v4) (coe v7)))))))))
-- Algebra.Apartness.Bundles.HeytingField._.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_286 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
d_'42''45'isCommutativeSemigroup_286 ~v0 ~v1 ~v2 v3
  = du_'42''45'isCommutativeSemigroup_286 v3
du_'42''45'isCommutativeSemigroup_286 ::
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
du_'42''45'isCommutativeSemigroup_286 v0
  = let v1 = d__'43'__240 (coe v0) in
    coe
      (let v2 = d__'42'__242 (coe v0) in
       coe
         (let v3 = d_'45'__244 (coe v0) in
          coe
            (let v4 = d_0'35'_246 (coe v0) in
             coe
               (let v5 = d_isHeytingField_250 (coe v0) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                             (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                                (coe v6) in
                      coe
                        (let v8
                               = coe
                                   MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_2946
                                   (coe v1) (coe v2) (coe v3) (coe v4) (coe v7) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1472
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1798
                                 (coe v8))))))))))
-- Algebra.Apartness.Bundles.HeytingField._.*-isMagma
d_'42''45'isMagma_288 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 -> MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'42''45'isMagma_288 ~v0 ~v1 ~v2 v3 = du_'42''45'isMagma_288 v3
du_'42''45'isMagma_288 ::
  T_HeytingField_208 -> MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_'42''45'isMagma_288 v0
  = let v1 = d__'43'__240 (coe v0) in
    coe
      (let v2 = d__'42'__242 (coe v0) in
       coe
         (let v3 = d_'45'__244 (coe v0) in
          coe
            (let v4 = d_0'35'_246 (coe v0) in
             coe
               (let v5 = d_isHeytingField_250 (coe v0) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                             (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                                (coe v6) in
                      coe
                        (let v8 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v7) in
                         coe
                           (let v9
                                  = coe
                                      MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                                      (coe v8) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1280
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2406 (coe v1)
                                    (coe v2) (coe v3) (coe v4) (coe v9)))))))))))
-- Algebra.Apartness.Bundles.HeytingField._.*-isMonoid
d_'42''45'isMonoid_290 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
d_'42''45'isMonoid_290 ~v0 ~v1 ~v2 v3 = du_'42''45'isMonoid_290 v3
du_'42''45'isMonoid_290 ::
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
du_'42''45'isMonoid_290 v0
  = let v1 = d__'43'__240 (coe v0) in
    coe
      (let v2 = d__'42'__242 (coe v0) in
       coe
         (let v3 = d_'45'__244 (coe v0) in
          coe
            (let v4 = d_0'35'_246 (coe v0) in
             coe
               (let v5 = d_isHeytingField_250 (coe v0) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                             (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                                (coe v6) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_2790 (coe v1)
                           (coe v2) (coe v3) (coe v4)
                           (coe MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v7)))))))))
-- Algebra.Apartness.Bundles.HeytingField._.*-isSemigroup
d_'42''45'isSemigroup_292 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_'42''45'isSemigroup_292 ~v0 ~v1 ~v2 v3
  = du_'42''45'isSemigroup_292 v3
du_'42''45'isSemigroup_292 ::
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
du_'42''45'isSemigroup_292 v0
  = let v1 = d__'43'__240 (coe v0) in
    coe
      (let v2 = d__'42'__242 (coe v0) in
       coe
         (let v3 = d_'45'__244 (coe v0) in
          coe
            (let v4 = d_0'35'_246 (coe v0) in
             coe
               (let v5 = d_isHeytingField_250 (coe v0) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                             (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                                (coe v6) in
                      coe
                        (let v8 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v7) in
                         coe
                           (let v9
                                  = coe
                                      MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                                      (coe v8) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1282
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2406 (coe v1)
                                    (coe v2) (coe v3) (coe v4) (coe v9)))))))))))
-- Algebra.Apartness.Bundles.HeytingField._.assoc
d_assoc_294 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_294 ~v0 ~v1 ~v2 v3 = du_assoc_294 v3
du_assoc_294 ::
  T_HeytingField_208 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_assoc_294 v0
  = let v1 = d_isHeytingField_250 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                    (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.d_assoc_480
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                              (coe v4)))))))))
-- Algebra.Apartness.Bundles.HeytingField._.comm
d_comm_296 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_296 ~v0 ~v1 ~v2 v3 = du_comm_296 v3
du_comm_296 :: T_HeytingField_208 -> AgdaAny -> AgdaAny -> AgdaAny
du_comm_296 v0
  = let v1 = d_isHeytingField_250 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                    (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.d_comm_1144
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                     (coe v4))))))
-- Algebra.Apartness.Bundles.HeytingField._.∙-cong
d_'8729''45'cong_298 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_298 ~v0 ~v1 ~v2 v3 = du_'8729''45'cong_298 v3
du_'8729''45'cong_298 ::
  T_HeytingField_208 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong_298 v0
  = let v1 = d_isHeytingField_250 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                    (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isMagma_478
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                                 (coe v4))))))))))
-- Algebra.Apartness.Bundles.HeytingField._.∙-congʳ
d_'8729''45'cong'691'_300 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_300 ~v0 ~v1 ~v2 v3
  = du_'8729''45'cong'691'_300 v3
du_'8729''45'cong'691'_300 ::
  T_HeytingField_208 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_300 v0
  = let v1 = d_isHeytingField_250 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                    (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v3) in
             coe
               (let v5
                      = coe
                          MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                             (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v6) in
                      coe
                        (let v8
                               = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v7) in
                         coe
                           (let v9
                                  = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v8) in
                            coe
                              (let v10
                                     = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v9) in
                               coe
                                 (let v11
                                        = coe
                                            MAlonzo.Code.Algebra.Structures.du_setoid_200
                                            (coe v10) in
                                  coe
                                    (let v12
                                           = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                               (coe v10) in
                                     coe
                                       (coe
                                          MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                                          (coe v12)
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                (coe v11)))))))))))))))
-- Algebra.Apartness.Bundles.HeytingField._.∙-congˡ
d_'8729''45'cong'737'_302 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_302 ~v0 ~v1 ~v2 v3
  = du_'8729''45'cong'737'_302 v3
du_'8729''45'cong'737'_302 ::
  T_HeytingField_208 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_302 v0
  = let v1 = d_isHeytingField_250 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                    (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v3) in
             coe
               (let v5
                      = coe
                          MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                             (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v6) in
                      coe
                        (let v8
                               = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v7) in
                         coe
                           (let v9
                                  = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v8) in
                            coe
                              (let v10
                                     = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v9) in
                               coe
                                 (let v11
                                        = coe
                                            MAlonzo.Code.Algebra.Structures.du_setoid_200
                                            (coe v10) in
                                  coe
                                    (let v12
                                           = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                               (coe v10) in
                                     coe
                                       (coe
                                          MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                                          (coe v12)
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                (coe v11)))))))))))))))
-- Algebra.Apartness.Bundles.HeytingField._.identity
d_identity_304 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_304 ~v0 ~v1 ~v2 v3 = du_identity_304 v3
du_identity_304 ::
  T_HeytingField_208 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_identity_304 v0
  = let v1 = d_isHeytingField_250 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                    (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.d_identity_696
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                           (coe v4))))))))
-- Algebra.Apartness.Bundles.HeytingField._.identityʳ
d_identity'691'_306 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 -> AgdaAny -> AgdaAny
d_identity'691'_306 ~v0 ~v1 ~v2 v3 = du_identity'691'_306 v3
du_identity'691'_306 :: T_HeytingField_208 -> AgdaAny -> AgdaAny
du_identity'691'_306 v0
  = let v1 = d_isHeytingField_250 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                    (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v3) in
             coe
               (let v5
                      = coe
                          MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                             (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v6) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_identity'691'_726
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v7)))))))))
-- Algebra.Apartness.Bundles.HeytingField._.identityˡ
d_identity'737'_308 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 -> AgdaAny -> AgdaAny
d_identity'737'_308 ~v0 ~v1 ~v2 v3 = du_identity'737'_308 v3
du_identity'737'_308 :: T_HeytingField_208 -> AgdaAny -> AgdaAny
du_identity'737'_308 v0
  = let v1 = d_isHeytingField_250 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                    (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v3) in
             coe
               (let v5
                      = coe
                          MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                             (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v6) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_identity'737'_724
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v7)))))))))
-- Algebra.Apartness.Bundles.HeytingField._.+-isAbelianGroup
d_'43''45'isAbelianGroup_310 ::
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1130
d_'43''45'isAbelianGroup_310 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
      (coe
         MAlonzo.Code.Algebra.Structures.d_isRing_2832
         (coe
            MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
            (coe
               MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
               (coe d_isHeytingField_250 (coe v0)))))
-- Algebra.Apartness.Bundles.HeytingField._.isCommutativeMagma
d_isCommutativeMagma_312 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
d_isCommutativeMagma_312 ~v0 ~v1 ~v2 v3
  = du_isCommutativeMagma_312 v3
du_isCommutativeMagma_312 ::
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
du_isCommutativeMagma_312 v0
  = let v1 = d_isHeytingField_250 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                    (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v3) in
             coe
               (let v5
                      = coe
                          MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                             (coe v5) in
                   coe
                     (let v7
                            = coe
                                MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1202
                                (coe v6) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_584
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_784
                              (coe v7)))))))))
-- Algebra.Apartness.Bundles.HeytingField._.isCommutativeMonoid
d_isCommutativeMonoid_314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
d_isCommutativeMonoid_314 ~v0 ~v1 ~v2 v3
  = du_isCommutativeMonoid_314 v3
du_isCommutativeMonoid_314 ::
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
du_isCommutativeMonoid_314 v0
  = let v1 = d_isHeytingField_250 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                    (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v3) in
             coe
               (let v5
                      = coe
                          MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1202
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                        (coe v5)))))))
-- Algebra.Apartness.Bundles.HeytingField._.isCommutativeSemigroup
d_isCommutativeSemigroup_316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
d_isCommutativeSemigroup_316 ~v0 ~v1 ~v2 v3
  = du_isCommutativeSemigroup_316 v3
du_isCommutativeSemigroup_316 ::
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
du_isCommutativeSemigroup_316 v0
  = let v1 = d_isHeytingField_250 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                    (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v3) in
             coe
               (let v5
                      = coe
                          MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                             (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_784
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1202
                           (coe v6))))))))
-- Algebra.Apartness.Bundles.HeytingField._.isGroup
d_isGroup_318 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1034
d_isGroup_318 ~v0 ~v1 ~v2 v3 = du_isGroup_318 v3
du_isGroup_318 ::
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1034
du_isGroup_318 v0
  = let v1 = d_isHeytingField_250 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                    (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                     (coe v4))))))
-- Algebra.Apartness.Bundles.HeytingField._.isInvertibleMagma
d_isInvertibleMagma_320 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_922
d_isInvertibleMagma_320 ~v0 ~v1 ~v2 v3
  = du_isInvertibleMagma_320 v3
du_isInvertibleMagma_320 ::
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_922
du_isInvertibleMagma_320 v0
  = let v1 = d_isHeytingField_250 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                    (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v3) in
             coe
               (let v5
                      = coe
                          MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                             (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_isInvertibleMagma_1120
                        (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v6))))))))
-- Algebra.Apartness.Bundles.HeytingField._.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_322 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_974
d_isInvertibleUnitalMagma_322 ~v0 ~v1 ~v2 v3
  = du_isInvertibleUnitalMagma_322 v3
du_isInvertibleUnitalMagma_322 ::
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_974
du_isInvertibleUnitalMagma_322 v0
  = let v1 = d_isHeytingField_250 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                    (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v3) in
             coe
               (let v5
                      = coe
                          MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                             (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_isInvertibleUnitalMagma_1122
                        (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v6))))))))
-- Algebra.Apartness.Bundles.HeytingField._.isMagma
d_isMagma_324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 -> MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_324 ~v0 ~v1 ~v2 v3 = du_isMagma_324 v3
du_isMagma_324 ::
  T_HeytingField_208 -> MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_isMagma_324 v0
  = let v1 = d_isHeytingField_250 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                    (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMagma_478
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                              (coe v4)))))))))
-- Algebra.Apartness.Bundles.HeytingField._.isMonoid
d_isMonoid_326 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
d_isMonoid_326 ~v0 ~v1 ~v2 v3 = du_isMonoid_326 v3
du_isMonoid_326 ::
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
du_isMonoid_326 v0
  = let v1 = d_isHeytingField_250 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                    (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                        (coe v4)))))))
-- Algebra.Apartness.Bundles.HeytingField._.isSemigroup
d_isSemigroup_328 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_isSemigroup_328 ~v0 ~v1 ~v2 v3 = du_isSemigroup_328 v3
du_isSemigroup_328 ::
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
du_isSemigroup_328 v0
  = let v1 = d_isHeytingField_250 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                    (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                           (coe v4))))))))
-- Algebra.Apartness.Bundles.HeytingField._.isUnitalMagma
d_isUnitalMagma_330 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_640
d_isUnitalMagma_330 ~v0 ~v1 ~v2 v3 = du_isUnitalMagma_330 v3
du_isUnitalMagma_330 ::
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_640
du_isUnitalMagma_330 v0
  = let v1 = d_isHeytingField_250 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                    (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v3) in
             coe
               (let v5
                      = coe
                          MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                             (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v6) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_728
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v7)))))))))
-- Algebra.Apartness.Bundles.HeytingField._.⁻¹-cong
d_'8315''185''45'cong_332 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'cong_332 ~v0 ~v1 ~v2 v3
  = du_'8315''185''45'cong_332 v3
du_'8315''185''45'cong_332 ::
  T_HeytingField_208 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8315''185''45'cong_332 v0
  = let v1 = d_isHeytingField_250 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                    (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'8315''185''45'cong_1052
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                        (coe v4)))))))
-- Algebra.Apartness.Bundles.HeytingField._.inverse
d_inverse_334 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_334 ~v0 ~v1 ~v2 v3 = du_inverse_334 v3
du_inverse_334 ::
  T_HeytingField_208 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inverse_334 v0
  = let v1 = d_isHeytingField_250 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                    (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.d_inverse_1050
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                        (coe v4)))))))
-- Algebra.Apartness.Bundles.HeytingField._.inverseʳ
d_inverse'691'_336 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 -> AgdaAny -> AgdaAny
d_inverse'691'_336 ~v0 ~v1 ~v2 v3 = du_inverse'691'_336 v3
du_inverse'691'_336 :: T_HeytingField_208 -> AgdaAny -> AgdaAny
du_inverse'691'_336 v0
  = let v1 = d_isHeytingField_250 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                    (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v3) in
             coe
               (let v5
                      = coe
                          MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                             (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_inverse'691'_1106
                        (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v6))))))))
-- Algebra.Apartness.Bundles.HeytingField._.inverseˡ
d_inverse'737'_338 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 -> AgdaAny -> AgdaAny
d_inverse'737'_338 ~v0 ~v1 ~v2 v3 = du_inverse'737'_338 v3
du_inverse'737'_338 :: T_HeytingField_208 -> AgdaAny -> AgdaAny
du_inverse'737'_338 v0
  = let v1 = d_isHeytingField_250 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                    (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v3) in
             coe
               (let v5
                      = coe
                          MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                             (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_inverse'737'_1104
                        (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v6))))))))
-- Algebra.Apartness.Bundles.HeytingField._.distrib
d_distrib_340 ::
  T_HeytingField_208 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_340 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_2700
      (coe
         MAlonzo.Code.Algebra.Structures.d_isRing_2832
         (coe
            MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
            (coe
               MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
               (coe d_isHeytingField_250 (coe v0)))))
-- Algebra.Apartness.Bundles.HeytingField._.distribʳ
d_distrib'691'_342 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_342 ~v0 ~v1 ~v2 v3 = du_distrib'691'_342 v3
du_distrib'691'_342 ::
  T_HeytingField_208 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'691'_342 v0
  = let v1 = d_isHeytingField_250 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                    (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_distrib'691'_2398
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                     (coe v4))))))
-- Algebra.Apartness.Bundles.HeytingField._.distribˡ
d_distrib'737'_344 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_344 ~v0 ~v1 ~v2 v3 = du_distrib'737'_344 v3
du_distrib'737'_344 ::
  T_HeytingField_208 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'737'_344 v0
  = let v1 = d_isHeytingField_250 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                    (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_distrib'737'_2396
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                     (coe v4))))))
-- Algebra.Apartness.Bundles.HeytingField._.invertible⇒#
d_invertible'8658''35'_346 ::
  T_HeytingField_208 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_invertible'8658''35'_346 v0
  = coe
      MAlonzo.Code.Algebra.Apartness.Structures.d_invertible'8658''35'_460
      (coe
         MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
         (coe d_isHeytingField_250 (coe v0)))
-- Algebra.Apartness.Bundles.HeytingField._.isApartnessRelation
d_isApartnessRelation_348 ::
  T_HeytingField_208 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722
d_isApartnessRelation_348 v0
  = coe
      MAlonzo.Code.Algebra.Apartness.Structures.d_isApartnessRelation_314
      (coe
         MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
         (coe d_isHeytingField_250 (coe v0)))
-- Algebra.Apartness.Bundles.HeytingField._.isCommutativeRing
d_isCommutativeRing_350 ::
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816
d_isCommutativeRing_350 v0
  = coe
      MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
      (coe
         MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
         (coe d_isHeytingField_250 (coe v0)))
-- Algebra.Apartness.Bundles.HeytingField._.isCommutativeSemiring
d_isCommutativeSemiring_352 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1696
d_isCommutativeSemiring_352 ~v0 ~v1 ~v2 v3
  = du_isCommutativeSemiring_352 v3
du_isCommutativeSemiring_352 ::
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1696
du_isCommutativeSemiring_352 v0
  = let v1 = d__'43'__240 (coe v0) in
    coe
      (let v2 = d__'42'__242 (coe v0) in
       coe
         (let v3 = d_'45'__244 (coe v0) in
          coe
            (let v4 = d_0'35'_246 (coe v0) in
             coe
               (let v5 = d_isHeytingField_250 (coe v0) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                             (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_2946
                        (coe v1) (coe v2) (coe v3) (coe v4)
                        (coe
                           MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                           (coe v6))))))))
-- Algebra.Apartness.Bundles.HeytingField._.isCommutativeSemiringWithoutOne
d_isCommutativeSemiringWithoutOne_354 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1390
d_isCommutativeSemiringWithoutOne_354 ~v0 ~v1 ~v2 v3
  = du_isCommutativeSemiringWithoutOne_354 v3
du_isCommutativeSemiringWithoutOne_354 ::
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1390
du_isCommutativeSemiringWithoutOne_354 v0
  = let v1 = d__'43'__240 (coe v0) in
    coe
      (let v2 = d__'42'__242 (coe v0) in
       coe
         (let v3 = d_'45'__244 (coe v0) in
          coe
            (let v4 = d_0'35'_246 (coe v0) in
             coe
               (let v5 = d_isHeytingField_250 (coe v0) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                             (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                                (coe v6) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1798
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_2946
                              (coe v1) (coe v2) (coe v3) (coe v4) (coe v7)))))))))
-- Algebra.Apartness.Bundles.HeytingField._.isEquivalence
d_isEquivalence_356 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_356 ~v0 ~v1 ~v2 v3 = du_isEquivalence_356 v3
du_isEquivalence_356 ::
  T_HeytingField_208 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_356 v0
  = let v1 = d_isHeytingField_250 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                    (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isMagma_478
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                                 (coe v4))))))))))
-- Algebra.Apartness.Bundles.HeytingField._.isHeytingCommutativeRing
d_isHeytingCommutativeRing_358 ::
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Apartness.Structures.T_IsHeytingCommutativeRing_160
d_isHeytingCommutativeRing_358 v0
  = coe
      MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
      (coe d_isHeytingField_250 (coe v0))
-- Algebra.Apartness.Bundles.HeytingField._.isNearSemiring
d_isNearSemiring_360 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1216
d_isNearSemiring_360 ~v0 ~v1 ~v2 v3 = du_isNearSemiring_360 v3
du_isNearSemiring_360 ::
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1216
du_isNearSemiring_360 v0
  = let v1 = d__'43'__240 (coe v0) in
    coe
      (let v2 = d__'42'__242 (coe v0) in
       coe
         (let v3 = d_'45'__244 (coe v0) in
          coe
            (let v4 = d_0'35'_246 (coe v0) in
             coe
               (let v5 = d_isHeytingField_250 (coe v0) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                             (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                                (coe v6) in
                      coe
                        (let v8 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v7) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2406 (coe v1)
                              (coe v2) (coe v3) (coe v4)
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                                 (coe v8))))))))))
-- Algebra.Apartness.Bundles.HeytingField._.isPartialEquivalence
d_isPartialEquivalence_362 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_362 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_362 v3
du_isPartialEquivalence_362 ::
  T_HeytingField_208 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_362 v0
  = let v1 = d_isHeytingField_250 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                    (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v3) in
             coe
               (let v5
                      = coe
                          MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                             (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v6) in
                      coe
                        (let v8
                               = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v7) in
                         coe
                           (let v9
                                  = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v8) in
                            coe
                              (let v10
                                     = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v9) in
                               coe
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                       (coe v10))))))))))))
-- Algebra.Apartness.Bundles.HeytingField._.isRing
d_isRing_364 ::
  T_HeytingField_208 -> MAlonzo.Code.Algebra.Structures.T_IsRing_2670
d_isRing_364 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isRing_2832
      (coe
         MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
         (coe
            MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
            (coe d_isHeytingField_250 (coe v0))))
-- Algebra.Apartness.Bundles.HeytingField._.isRingWithoutOne
d_isRingWithoutOne_366 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2304
d_isRingWithoutOne_366 ~v0 ~v1 ~v2 v3 = du_isRingWithoutOne_366 v3
du_isRingWithoutOne_366 ::
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2304
du_isRingWithoutOne_366 v0
  = let v1 = d_isHeytingField_250 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
               (coe MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v3)))))
-- Algebra.Apartness.Bundles.HeytingField._.isSemiring
d_isSemiring_368 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1588
d_isSemiring_368 ~v0 ~v1 ~v2 v3 = du_isSemiring_368 v3
du_isSemiring_368 ::
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1588
du_isSemiring_368 v0
  = let v1 = d__'43'__240 (coe v0) in
    coe
      (let v2 = d__'42'__242 (coe v0) in
       coe
         (let v3 = d_'45'__244 (coe v0) in
          coe
            (let v4 = d_0'35'_246 (coe v0) in
             coe
               (let v5 = d_isHeytingField_250 (coe v0) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                             (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                                (coe v6) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_isSemiring_2800 (coe v1)
                           (coe v2) (coe v3) (coe v4)
                           (coe MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v7)))))))))
-- Algebra.Apartness.Bundles.HeytingField._.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_370 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1486
d_isSemiringWithoutAnnihilatingZero_370 ~v0 ~v1 ~v2 v3
  = du_isSemiringWithoutAnnihilatingZero_370 v3
du_isSemiringWithoutAnnihilatingZero_370 ::
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1486
du_isSemiringWithoutAnnihilatingZero_370 v0
  = let v1 = d_isHeytingField_250 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutAnnihilatingZero_2798
               (coe MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v3)))))
-- Algebra.Apartness.Bundles.HeytingField._.isSemiringWithoutOne
d_isSemiringWithoutOne_372 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1296
d_isSemiringWithoutOne_372 ~v0 ~v1 ~v2 v3
  = du_isSemiringWithoutOne_372 v3
du_isSemiringWithoutOne_372 ::
  T_HeytingField_208 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1296
du_isSemiringWithoutOne_372 v0
  = let v1 = d__'43'__240 (coe v0) in
    coe
      (let v2 = d__'42'__242 (coe v0) in
       coe
         (let v3 = d_'45'__244 (coe v0) in
          coe
            (let v4 = d_0'35'_246 (coe v0) in
             coe
               (let v5 = d_isHeytingField_250 (coe v0) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                             (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                                (coe v6) in
                      coe
                        (let v8 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v7) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1678
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_isSemiring_2800 (coe v1)
                                 (coe v2) (coe v3) (coe v4) (coe v8))))))))))
-- Algebra.Apartness.Bundles.HeytingField._.refl
d_refl_374 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 -> AgdaAny -> AgdaAny
d_refl_374 ~v0 ~v1 ~v2 v3 = du_refl_374 v3
du_refl_374 :: T_HeytingField_208 -> AgdaAny -> AgdaAny
du_refl_374 v0
  = let v1 = d_isHeytingField_250 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                    (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isMagma_478
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                                    (coe v4)))))))))))
-- Algebra.Apartness.Bundles.HeytingField._.reflexive
d_reflexive_376 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_376 ~v0 ~v1 ~v2 v3 = du_reflexive_376 v3
du_reflexive_376 ::
  T_HeytingField_208 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_376 v0
  = let v1 = d_isHeytingField_250 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                    (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v3) in
             coe
               (let v5
                      = coe
                          MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                             (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v6) in
                      coe
                        (let v8
                               = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v7) in
                         coe
                           (let v9
                                  = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v8) in
                            coe
                              (let v10
                                     = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v9) in
                               coe
                                 (\ v11 v12 v13 ->
                                    coe
                                      MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                         (coe v10))
                                      v11))))))))))
-- Algebra.Apartness.Bundles.HeytingField._.setoid
d_setoid_378 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_378 ~v0 ~v1 ~v2 v3 = du_setoid_378 v3
du_setoid_378 ::
  T_HeytingField_208 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_378 v0
  = let v1 = d_isHeytingField_250 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                    (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v3) in
             coe
               (let v5
                      = coe
                          MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                             (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v6) in
                      coe
                        (let v8
                               = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v7) in
                         coe
                           (let v9
                                  = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v8) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_setoid_200
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v9)))))))))))
-- Algebra.Apartness.Bundles.HeytingField._.sym
d_sym_380 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_380 ~v0 ~v1 ~v2 v3 = du_sym_380 v3
du_sym_380 ::
  T_HeytingField_208 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_380 v0
  = let v1 = d_isHeytingField_250 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                    (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isMagma_478
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                                    (coe v4)))))))))))
-- Algebra.Apartness.Bundles.HeytingField._.tight
d_tight_382 ::
  T_HeytingField_208 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_tight_382 v0
  = coe
      MAlonzo.Code.Algebra.Apartness.Structures.d_tight_472
      (coe d_isHeytingField_250 (coe v0))
-- Algebra.Apartness.Bundles.HeytingField._.trans
d_trans_384 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_384 ~v0 ~v1 ~v2 v3 = du_trans_384 v3
du_trans_384 ::
  T_HeytingField_208 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_384 v0
  = let v1 = d_isHeytingField_250 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                    (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isMagma_478
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                                    (coe v4)))))))))))
-- Algebra.Apartness.Bundles.HeytingField._.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_386 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'691''45''8315''185'_386 ~v0 ~v1 ~v2 v3
  = du_unique'691''45''8315''185'_386 v3
du_unique'691''45''8315''185'_386 ::
  T_HeytingField_208 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'691''45''8315''185'_386 v0
  = let v1 = d__'43'__240 (coe v0) in
    coe
      (let v2 = d_'45'__244 (coe v0) in
       coe
         (let v3 = d_0'35'_246 (coe v0) in
          coe
            (let v4 = d_isHeytingField_250 (coe v0) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                             (coe v5) in
                   coe
                     (let v7 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v6) in
                      coe
                        (let v8
                               = coe
                                   MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                                   (coe v7) in
                         coe
                           (let v9
                                  = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                      (coe v8) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_unique'691''45''8315''185'_1118
                                 (coe v1) (coe v3) (coe v2)
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                                    (coe v9)))))))))))
-- Algebra.Apartness.Bundles.HeytingField._.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_388 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'737''45''8315''185'_388 ~v0 ~v1 ~v2 v3
  = du_unique'737''45''8315''185'_388 v3
du_unique'737''45''8315''185'_388 ::
  T_HeytingField_208 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'737''45''8315''185'_388 v0
  = let v1 = d__'43'__240 (coe v0) in
    coe
      (let v2 = d_'45'__244 (coe v0) in
       coe
         (let v3 = d_0'35'_246 (coe v0) in
          coe
            (let v4 = d_isHeytingField_250 (coe v0) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                             (coe v5) in
                   coe
                     (let v7 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v6) in
                      coe
                        (let v8
                               = coe
                                   MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                                   (coe v7) in
                         coe
                           (let v9
                                  = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                      (coe v8) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_unique'737''45''8315''185'_1112
                                 (coe v1) (coe v3) (coe v2)
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                                    (coe v9)))))))))))
-- Algebra.Apartness.Bundles.HeytingField._.zero
d_zero_390 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_390 ~v0 ~v1 ~v2 v3 = du_zero_390 v3
du_zero_390 ::
  T_HeytingField_208 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_zero_390 v0
  = let v1 = d__'43'__240 (coe v0) in
    coe
      (let v2 = d__'42'__242 (coe v0) in
       coe
         (let v3 = d_'45'__244 (coe v0) in
          coe
            (let v4 = d_0'35'_246 (coe v0) in
             coe
               (let v5 = d_isHeytingField_250 (coe v0) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                             (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                                (coe v6) in
                      coe
                        (let v8 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v7) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_zero_2404 (coe v1) (coe v2)
                              (coe v3) (coe v4)
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                                 (coe v8))))))))))
-- Algebra.Apartness.Bundles.HeytingField._.zeroʳ
d_zero'691'_392 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 -> AgdaAny -> AgdaAny
d_zero'691'_392 ~v0 ~v1 ~v2 v3 = du_zero'691'_392 v3
du_zero'691'_392 :: T_HeytingField_208 -> AgdaAny -> AgdaAny
du_zero'691'_392 v0
  = let v1 = d__'43'__240 (coe v0) in
    coe
      (let v2 = d__'42'__242 (coe v0) in
       coe
         (let v3 = d_'45'__244 (coe v0) in
          coe
            (let v4 = d_0'35'_246 (coe v0) in
             coe
               (let v5 = d_isHeytingField_250 (coe v0) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                             (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                                (coe v6) in
                      coe
                        (let v8 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v7) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_zero'691'_2402 (coe v1) (coe v2)
                              (coe v3) (coe v4)
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                                 (coe v8))))))))))
-- Algebra.Apartness.Bundles.HeytingField._.zeroˡ
d_zero'737'_394 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 -> AgdaAny -> AgdaAny
d_zero'737'_394 ~v0 ~v1 ~v2 v3 = du_zero'737'_394 v3
du_zero'737'_394 :: T_HeytingField_208 -> AgdaAny -> AgdaAny
du_zero'737'_394 v0
  = let v1 = d__'43'__240 (coe v0) in
    coe
      (let v2 = d__'42'__242 (coe v0) in
       coe
         (let v3 = d_'45'__244 (coe v0) in
          coe
            (let v4 = d_0'35'_246 (coe v0) in
             coe
               (let v5 = d_isHeytingField_250 (coe v0) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
                             (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Apartness.Structures.d_isCommutativeRing_312
                                (coe v6) in
                      coe
                        (let v8 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v7) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_zero'737'_2400 (coe v1) (coe v2)
                              (coe v3) (coe v4)
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                                 (coe v8))))))))))
-- Algebra.Apartness.Bundles.HeytingField._.¬#-isEquivalence
d_'172''35''45'isEquivalence_396 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_'172''35''45'isEquivalence_396 ~v0 ~v1 ~v2 ~v3
  = du_'172''35''45'isEquivalence_396
du_'172''35''45'isEquivalence_396 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_'172''35''45'isEquivalence_396
  = coe
      MAlonzo.Code.Algebra.Apartness.Structures.du_'172''35''45'isEquivalence_462
-- Algebra.Apartness.Bundles.HeytingField.heytingCommutativeRing
d_heytingCommutativeRing_398 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 -> T_HeytingCommutativeRing_12
d_heytingCommutativeRing_398 ~v0 ~v1 ~v2 v3
  = du_heytingCommutativeRing_398 v3
du_heytingCommutativeRing_398 ::
  T_HeytingField_208 -> T_HeytingCommutativeRing_12
du_heytingCommutativeRing_398 v0
  = coe
      C_HeytingCommutativeRing'46'constructor_657 (d__'43'__240 (coe v0))
      (d__'42'__242 (coe v0)) (d_'45'__244 (coe v0))
      (d_0'35'_246 (coe v0)) (d_1'35'_248 (coe v0))
      (MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
         (coe d_isHeytingField_250 (coe v0)))
-- Algebra.Apartness.Bundles.HeytingField.apartnessRelation
d_apartnessRelation_400 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingField_208 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_ApartnessRelation_1484
d_apartnessRelation_400 ~v0 ~v1 ~v2 v3
  = du_apartnessRelation_400 v3
du_apartnessRelation_400 ::
  T_HeytingField_208 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_ApartnessRelation_1484
du_apartnessRelation_400 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_ApartnessRelation'46'constructor_28831
      (MAlonzo.Code.Algebra.Apartness.Structures.d_isApartnessRelation_314
         (coe
            MAlonzo.Code.Algebra.Apartness.Structures.d_isHeytingCommutativeRing_470
            (coe d_isHeytingField_250 (coe v0))))
