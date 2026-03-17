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

module MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Bundles
import qualified MAlonzo.Code.Algebra.Bundles.Raw
import qualified MAlonzo.Code.Algebra.Consequences.Base
import qualified MAlonzo.Code.Algebra.Properties.AbelianGroup
import qualified MAlonzo.Code.Algebra.Properties.RingWithoutOne
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing
d_IsAlmostCommutativeRing_26 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_IsAlmostCommutativeRing_26
  = C_IsAlmostCommutativeRing'46'constructor_1027 MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1696
                                                  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                                  (AgdaAny -> AgdaAny -> AgdaAny)
                                                  (AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing.isCommutativeSemiring
d_isCommutativeSemiring_62 ::
  T_IsAlmostCommutativeRing_26 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1696
d_isCommutativeSemiring_62 v0
  = case coe v0 of
      C_IsAlmostCommutativeRing'46'constructor_1027 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing.-‿cong
d_'45''8255'cong_64 ::
  T_IsAlmostCommutativeRing_26 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'45''8255'cong_64 v0
  = case coe v0 of
      C_IsAlmostCommutativeRing'46'constructor_1027 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing.-‿*-distribˡ
d_'45''8255''42''45'distrib'737'_70 ::
  T_IsAlmostCommutativeRing_26 -> AgdaAny -> AgdaAny -> AgdaAny
d_'45''8255''42''45'distrib'737'_70 v0
  = case coe v0 of
      C_IsAlmostCommutativeRing'46'constructor_1027 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing.-‿+-comm
d_'45''8255''43''45'comm_76 ::
  T_IsAlmostCommutativeRing_26 -> AgdaAny -> AgdaAny -> AgdaAny
d_'45''8255''43''45'comm_76 v0
  = case coe v0 of
      C_IsAlmostCommutativeRing'46'constructor_1027 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.*-assoc
d_'42''45'assoc_80 ::
  T_IsAlmostCommutativeRing_26 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_80 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'assoc_1510
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
            (coe d_isCommutativeSemiring_62 (coe v0))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.*-comm
d_'42''45'comm_82 ::
  T_IsAlmostCommutativeRing_26 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'comm_82 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'comm_1712
      (coe d_isCommutativeSemiring_62 (coe v0))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.*-cong
d_'42''45'cong_84 ::
  T_IsAlmostCommutativeRing_26 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_84 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'cong_1508
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
            (coe d_isCommutativeSemiring_62 (coe v0))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.∙-congʳ
d_'8729''45'cong'691'_86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsAlmostCommutativeRing_26 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_86 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'691'_86 v9
du_'8729''45'cong'691'_86 ::
  T_IsAlmostCommutativeRing_26 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_86 v0
  = let v1 = d_isCommutativeSemiring_62 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                    (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1568
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v4) in
                coe
                  (let v6 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v5) in
                   coe
                     (let v7
                            = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v6) in
                      coe
                        (let v8
                               = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 (coe v6) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                              (coe v8)
                              (coe
                                 MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                    (coe v7)))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.∙-congˡ
d_'8729''45'cong'737'_88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsAlmostCommutativeRing_26 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_88 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'737'_88 v9
du_'8729''45'cong'737'_88 ::
  T_IsAlmostCommutativeRing_26 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_88 v0
  = let v1 = d_isCommutativeSemiring_62 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                    (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1568
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v4) in
                coe
                  (let v6 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v5) in
                   coe
                     (let v7
                            = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v6) in
                      coe
                        (let v8
                               = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 (coe v6) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                              (coe v8)
                              (coe
                                 MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                    (coe v7)))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.*-identity
d_'42''45'identity_90 ::
  T_IsAlmostCommutativeRing_26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_90 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1512
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
            (coe d_isCommutativeSemiring_62 (coe v0))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.identityʳ
d_identity'691'_92 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsAlmostCommutativeRing_26 -> AgdaAny -> AgdaAny
d_identity'691'_92 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'691'_92 v9
du_identity'691'_92 ::
  T_IsAlmostCommutativeRing_26 -> AgdaAny -> AgdaAny
du_identity'691'_92 v0
  = let v1 = d_isCommutativeSemiring_62 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_identity'691'_726
               (coe
                  MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1568
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.identityˡ
d_identity'737'_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsAlmostCommutativeRing_26 -> AgdaAny -> AgdaAny
d_identity'737'_94 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'737'_94 v9
du_identity'737'_94 ::
  T_IsAlmostCommutativeRing_26 -> AgdaAny -> AgdaAny
du_identity'737'_94 v0
  = let v1 = d_isCommutativeSemiring_62 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_identity'737'_724
               (coe
                  MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1568
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.isCommutativeMagma
d_isCommutativeMagma_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsAlmostCommutativeRing_26 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
d_isCommutativeMagma_96 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isCommutativeMagma_96 v9
du_isCommutativeMagma_96 ::
  T_IsAlmostCommutativeRing_26 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
du_isCommutativeMagma_96 v0
  = let v1 = d_isCommutativeSemiring_62 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1798
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_584
            (coe
               MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1472
               (coe v2))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.*-isCommutativeMonoid
d_'42''45'isCommutativeMonoid_98 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsAlmostCommutativeRing_26 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
d_'42''45'isCommutativeMonoid_98 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                 ~v8 v9
  = du_'42''45'isCommutativeMonoid_98 v9
du_'42''45'isCommutativeMonoid_98 ::
  T_IsAlmostCommutativeRing_26 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
du_'42''45'isCommutativeMonoid_98 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeMonoid_1806
      (coe d_isCommutativeSemiring_62 (coe v0))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsAlmostCommutativeRing_26 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
d_'42''45'isCommutativeSemigroup_100 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                     ~v7 ~v8 v9
  = du_'42''45'isCommutativeSemigroup_100 v9
du_'42''45'isCommutativeSemigroup_100 ::
  T_IsAlmostCommutativeRing_26 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
du_'42''45'isCommutativeSemigroup_100 v0
  = let v1 = d_isCommutativeSemiring_62 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1472
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1798
            (coe v1)))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.*-isMagma
d_'42''45'isMagma_102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsAlmostCommutativeRing_26 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'42''45'isMagma_102 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'42''45'isMagma_102 v9
du_'42''45'isMagma_102 ::
  T_IsAlmostCommutativeRing_26 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_'42''45'isMagma_102 v0
  = let v1 = d_isCommutativeSemiring_62 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1564
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
               (coe v2))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.*-isMonoid
d_'42''45'isMonoid_104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsAlmostCommutativeRing_26 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
d_'42''45'isMonoid_104 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'42''45'isMonoid_104 v9
du_'42''45'isMonoid_104 ::
  T_IsAlmostCommutativeRing_26 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
du_'42''45'isMonoid_104 v0
  = let v1 = d_isCommutativeSemiring_62 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1568
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
               (coe v2))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.*-isSemigroup
d_'42''45'isSemigroup_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsAlmostCommutativeRing_26 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_'42''45'isSemigroup_106 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'42''45'isSemigroup_106 v9
du_'42''45'isSemigroup_106 ::
  T_IsAlmostCommutativeRing_26 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
du_'42''45'isSemigroup_106 v0
  = let v1 = d_isCommutativeSemiring_62 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1566
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
               (coe v2))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.assoc
d_assoc_108 ::
  T_IsAlmostCommutativeRing_26 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_108 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_assoc_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_744
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                     (coe d_isCommutativeSemiring_62 (coe v0)))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.comm
d_comm_110 ::
  T_IsAlmostCommutativeRing_26 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_110 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_comm_746
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
               (coe d_isCommutativeSemiring_62 (coe v0)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.∙-cong
d_'8729''45'cong_112 ::
  T_IsAlmostCommutativeRing_26 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_112 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_478
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_744
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                        (coe d_isCommutativeSemiring_62 (coe v0))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.∙-congʳ
d_'8729''45'cong'691'_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsAlmostCommutativeRing_26 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_114 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'691'_114 v9
du_'8729''45'cong'691'_114 ::
  T_IsAlmostCommutativeRing_26 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_114 v0
  = let v1 = d_isCommutativeSemiring_62 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v5) in
                   coe
                     (let v7 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v6) in
                      coe
                        (let v8
                               = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v7) in
                         coe
                           (let v9
                                  = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 (coe v7) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                                 (coe v9)
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                       (coe v8))))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.∙-congˡ
d_'8729''45'cong'737'_116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsAlmostCommutativeRing_26 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_116 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'737'_116 v9
du_'8729''45'cong'737'_116 ::
  T_IsAlmostCommutativeRing_26 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_116 v0
  = let v1 = d_isCommutativeSemiring_62 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v5) in
                   coe
                     (let v7 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v6) in
                      coe
                        (let v8
                               = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v7) in
                         coe
                           (let v9
                                  = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 (coe v7) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                                 (coe v9)
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                       (coe v8))))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.identity
d_identity_118 ::
  T_IsAlmostCommutativeRing_26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_118 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_696
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_744
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                  (coe d_isCommutativeSemiring_62 (coe v0))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.identityʳ
d_identity'691'_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsAlmostCommutativeRing_26 -> AgdaAny -> AgdaAny
d_identity'691'_120 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'691'_120 v9
du_identity'691'_120 ::
  T_IsAlmostCommutativeRing_26 -> AgdaAny -> AgdaAny
du_identity'691'_120 v0
  = let v1 = d_isCommutativeSemiring_62 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_identity'691'_726
                  (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v4))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.identityˡ
d_identity'737'_122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsAlmostCommutativeRing_26 -> AgdaAny -> AgdaAny
d_identity'737'_122 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'737'_122 v9
du_identity'737'_122 ::
  T_IsAlmostCommutativeRing_26 -> AgdaAny -> AgdaAny
du_identity'737'_122 v0
  = let v1 = d_isCommutativeSemiring_62 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_identity'737'_724
                  (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v4))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.isCommutativeMagma
d_isCommutativeMagma_124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsAlmostCommutativeRing_26 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
d_isCommutativeMagma_124 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isCommutativeMagma_124 v9
du_isCommutativeMagma_124 ::
  T_IsAlmostCommutativeRing_26 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
du_isCommutativeMagma_124 v0
  = let v1 = d_isCommutativeSemiring_62 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_584
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_784
                     (coe v4))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_126 ::
  T_IsAlmostCommutativeRing_26 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
d_'43''45'isCommutativeMonoid_126 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
            (coe d_isCommutativeSemiring_62 (coe v0))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.isCommutativeSemigroup
d_isCommutativeSemigroup_128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsAlmostCommutativeRing_26 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
d_isCommutativeSemigroup_128 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isCommutativeSemigroup_128 v9
du_isCommutativeSemigroup_128 ::
  T_IsAlmostCommutativeRing_26 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
du_isCommutativeSemigroup_128 v0
  = let v1 = d_isCommutativeSemiring_62 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_784
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.isMagma
d_isMagma_130 ::
  T_IsAlmostCommutativeRing_26 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_130 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_478
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_744
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                     (coe d_isCommutativeSemiring_62 (coe v0)))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.isMonoid
d_isMonoid_132 ::
  T_IsAlmostCommutativeRing_26 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
d_isMonoid_132 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_744
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
               (coe d_isCommutativeSemiring_62 (coe v0)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.isSemigroup
d_isSemigroup_134 ::
  T_IsAlmostCommutativeRing_26 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_isSemigroup_134 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_744
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                  (coe d_isCommutativeSemiring_62 (coe v0))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.isUnitalMagma
d_isUnitalMagma_136 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsAlmostCommutativeRing_26 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_640
d_isUnitalMagma_136 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isUnitalMagma_136 v9
du_isUnitalMagma_136 ::
  T_IsAlmostCommutativeRing_26 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_640
du_isUnitalMagma_136 v0
  = let v1 = d_isCommutativeSemiring_62 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_728
                  (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v4))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.distrib
d_distrib_138 ::
  T_IsAlmostCommutativeRing_26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_138 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1514
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
            (coe d_isCommutativeSemiring_62 (coe v0))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.distribʳ
d_distrib'691'_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsAlmostCommutativeRing_26 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_140 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_distrib'691'_140 v9
du_distrib'691'_140 ::
  T_IsAlmostCommutativeRing_26 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'691'_140 v0
  = let v1 = d_isCommutativeSemiring_62 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_distrib'691'_1518
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
               (coe v2))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.distribˡ
d_distrib'737'_142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsAlmostCommutativeRing_26 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_142 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_distrib'737'_142 v9
du_distrib'737'_142 ::
  T_IsAlmostCommutativeRing_26 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'737'_142 v0
  = let v1 = d_isCommutativeSemiring_62 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_distrib'737'_1516
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
               (coe v2))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.isCommutativeSemiringWithoutOne
d_isCommutativeSemiringWithoutOne_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsAlmostCommutativeRing_26 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1390
d_isCommutativeSemiringWithoutOne_144 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                      ~v7 ~v8 v9
  = du_isCommutativeSemiringWithoutOne_144 v9
du_isCommutativeSemiringWithoutOne_144 ::
  T_IsAlmostCommutativeRing_26 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1390
du_isCommutativeSemiringWithoutOne_144 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1798
      (coe d_isCommutativeSemiring_62 (coe v0))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.isEquivalence
d_isEquivalence_146 ::
  T_IsAlmostCommutativeRing_26 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_146 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_478
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_744
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                        (coe d_isCommutativeSemiring_62 (coe v0))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.isNearSemiring
d_isNearSemiring_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsAlmostCommutativeRing_26 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1216
d_isNearSemiring_148 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isNearSemiring_148 v9
du_isNearSemiring_148 ::
  T_IsAlmostCommutativeRing_26 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1216
du_isNearSemiring_148 v0
  = let v1 = d_isCommutativeSemiring_62 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isNearSemiring_1382
            (coe
               MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1678
               (coe v2))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.isPartialEquivalence
d_isPartialEquivalence_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsAlmostCommutativeRing_26 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_150 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isPartialEquivalence_150 v9
du_isPartialEquivalence_150 ::
  T_IsAlmostCommutativeRing_26 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_150 v0
  = let v1 = d_isCommutativeSemiring_62 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v5) in
                   coe
                     (let v7 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v6) in
                      coe
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                              (coe v7)))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.isSemiring
d_isSemiring_152 ::
  T_IsAlmostCommutativeRing_26 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1588
d_isSemiring_152 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
      (coe d_isCommutativeSemiring_62 (coe v0))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_154 ::
  T_IsAlmostCommutativeRing_26 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1486
d_isSemiringWithoutAnnihilatingZero_154 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
         (coe d_isCommutativeSemiring_62 (coe v0)))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.isSemiringWithoutOne
d_isSemiringWithoutOne_156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsAlmostCommutativeRing_26 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1296
d_isSemiringWithoutOne_156 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isSemiringWithoutOne_156 v9
du_isSemiringWithoutOne_156 ::
  T_IsAlmostCommutativeRing_26 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1296
du_isSemiringWithoutOne_156 v0
  = let v1 = d_isCommutativeSemiring_62 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1678
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v1)))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.refl
d_refl_158 :: T_IsAlmostCommutativeRing_26 -> AgdaAny -> AgdaAny
d_refl_158 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_478
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                           (coe d_isCommutativeSemiring_62 (coe v0)))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.reflexive
d_reflexive_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsAlmostCommutativeRing_26 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_160 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_reflexive_160 v9
du_reflexive_160 ::
  T_IsAlmostCommutativeRing_26 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_160 v0
  = let v1 = d_isCommutativeSemiring_62 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v5) in
                   coe
                     (let v7 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v6) in
                      coe
                        (\ v8 v9 v10 ->
                           coe
                             MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                             (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v7))
                             v8)))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.setoid
d_setoid_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsAlmostCommutativeRing_26 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_162 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_setoid_162 v9
du_setoid_162 ::
  T_IsAlmostCommutativeRing_26 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_162 v0
  = let v1 = d_isCommutativeSemiring_62 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_setoid_200
                        (coe MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v6))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.sym
d_sym_164 ::
  T_IsAlmostCommutativeRing_26 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_164 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_478
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                           (coe d_isCommutativeSemiring_62 (coe v0)))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.trans
d_trans_166 ::
  T_IsAlmostCommutativeRing_26 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_166 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_478
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                           (coe d_isCommutativeSemiring_62 (coe v0)))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.zero
d_zero_168 ::
  T_IsAlmostCommutativeRing_26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_168 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_1604
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
         (coe d_isCommutativeSemiring_62 (coe v0)))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.zeroʳ
d_zero'691'_170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsAlmostCommutativeRing_26 -> AgdaAny -> AgdaAny
d_zero'691'_170 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_zero'691'_170 v9
du_zero'691'_170 ::
  T_IsAlmostCommutativeRing_26 -> AgdaAny -> AgdaAny
du_zero'691'_170 v0
  = let v1 = d_isCommutativeSemiring_62 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_zero'691'_1380
            (coe
               MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1678
               (coe v2))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.IsAlmostCommutativeRing._.zeroˡ
d_zero'737'_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsAlmostCommutativeRing_26 -> AgdaAny -> AgdaAny
d_zero'737'_172 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_zero'737'_172 v9
du_zero'737'_172 ::
  T_IsAlmostCommutativeRing_26 -> AgdaAny -> AgdaAny
du_zero'737'_172 v0
  = let v1 = d_isCommutativeSemiring_62 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_zero'737'_1378
            (coe
               MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1678
               (coe v2))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing
d_AlmostCommutativeRing_178 a0 a1 = ()
data T_AlmostCommutativeRing_178
  = C_AlmostCommutativeRing'46'constructor_5973 (AgdaAny ->
                                                 AgdaAny -> AgdaAny)
                                                (AgdaAny -> AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny)
                                                AgdaAny AgdaAny T_IsAlmostCommutativeRing_26
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing.Carrier
d_Carrier_200 :: T_AlmostCommutativeRing_178 -> ()
d_Carrier_200 = erased
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._≈_
d__'8776'__202 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny -> ()
d__'8776'__202 = erased
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._+_
d__'43'__204 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny -> AgdaAny
d__'43'__204 v0
  = case coe v0 of
      C_AlmostCommutativeRing'46'constructor_5973 v3 v4 v5 v6 v7 v8
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._*_
d__'42'__206 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny -> AgdaAny
d__'42'__206 v0
  = case coe v0 of
      C_AlmostCommutativeRing'46'constructor_5973 v3 v4 v5 v6 v7 v8
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing.-_
d_'45'__208 :: T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
d_'45'__208 v0
  = case coe v0 of
      C_AlmostCommutativeRing'46'constructor_5973 v3 v4 v5 v6 v7 v8
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing.0#
d_0'35'_210 :: T_AlmostCommutativeRing_178 -> AgdaAny
d_0'35'_210 v0
  = case coe v0 of
      C_AlmostCommutativeRing'46'constructor_5973 v3 v4 v5 v6 v7 v8
        -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing.1#
d_1'35'_212 :: T_AlmostCommutativeRing_178 -> AgdaAny
d_1'35'_212 v0
  = case coe v0 of
      C_AlmostCommutativeRing'46'constructor_5973 v3 v4 v5 v6 v7 v8
        -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing.isAlmostCommutativeRing
d_isAlmostCommutativeRing_214 ::
  T_AlmostCommutativeRing_178 -> T_IsAlmostCommutativeRing_26
d_isAlmostCommutativeRing_214 v0
  = case coe v0 of
      C_AlmostCommutativeRing'46'constructor_5973 v3 v4 v5 v6 v7 v8
        -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.*-assoc
d_'42''45'assoc_218 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_218 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'assoc_1510
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
            (coe
               d_isCommutativeSemiring_62
               (coe d_isAlmostCommutativeRing_214 (coe v0)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.*-comm
d_'42''45'comm_220 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'comm_220 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'comm_1712
      (coe
         d_isCommutativeSemiring_62
         (coe d_isAlmostCommutativeRing_214 (coe v0)))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.*-cong
d_'42''45'cong_222 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_222 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'cong_1508
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
            (coe
               d_isCommutativeSemiring_62
               (coe d_isAlmostCommutativeRing_214 (coe v0)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.∙-congʳ
d_'8729''45'cong'691'_224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_224 ~v0 ~v1 v2
  = du_'8729''45'cong'691'_224 v2
du_'8729''45'cong'691'_224 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_224 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = coe
                          MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1568
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v5) in
                   coe
                     (let v7 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v6) in
                      coe
                        (let v8
                               = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v7) in
                         coe
                           (let v9
                                  = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 (coe v7) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                                 (coe v9)
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                       (coe v8))))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.∙-congˡ
d_'8729''45'cong'737'_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_226 ~v0 ~v1 v2
  = du_'8729''45'cong'737'_226 v2
du_'8729''45'cong'737'_226 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_226 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = coe
                          MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1568
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v5) in
                   coe
                     (let v7 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v6) in
                      coe
                        (let v8
                               = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v7) in
                         coe
                           (let v9
                                  = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 (coe v7) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                                 (coe v9)
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                       (coe v8))))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.*-identity
d_'42''45'identity_228 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_228 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1512
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
            (coe
               d_isCommutativeSemiring_62
               (coe d_isAlmostCommutativeRing_214 (coe v0)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.identityʳ
d_identity'691'_230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
d_identity'691'_230 ~v0 ~v1 v2 = du_identity'691'_230 v2
du_identity'691'_230 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
du_identity'691'_230 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_identity'691'_726
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1568
                     (coe v4))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.identityˡ
d_identity'737'_232 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
d_identity'737'_232 ~v0 ~v1 v2 = du_identity'737'_232 v2
du_identity'737'_232 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
du_identity'737'_232 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_identity'737'_724
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1568
                     (coe v4))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.isCommutativeMagma
d_isCommutativeMagma_234 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
d_isCommutativeMagma_234 ~v0 ~v1 v2 = du_isCommutativeMagma_234 v2
du_isCommutativeMagma_234 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
du_isCommutativeMagma_234 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1798
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_584
               (coe
                  MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1472
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.*-isCommutativeMonoid
d_'42''45'isCommutativeMonoid_236 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
d_'42''45'isCommutativeMonoid_236 ~v0 ~v1 v2
  = du_'42''45'isCommutativeMonoid_236 v2
du_'42''45'isCommutativeMonoid_236 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
du_'42''45'isCommutativeMonoid_236 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeMonoid_1806
         (coe d_isCommutativeSemiring_62 (coe v1)))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_238 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
d_'42''45'isCommutativeSemigroup_238 ~v0 ~v1 v2
  = du_'42''45'isCommutativeSemigroup_238 v2
du_'42''45'isCommutativeSemigroup_238 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
du_'42''45'isCommutativeSemigroup_238 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1472
            (coe
               MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1798
               (coe v2))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.*-isMagma
d_'42''45'isMagma_240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'42''45'isMagma_240 ~v0 ~v1 v2 = du_'42''45'isMagma_240 v2
du_'42''45'isMagma_240 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_'42''45'isMagma_240 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1564
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.*-isMonoid
d_'42''45'isMonoid_242 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
d_'42''45'isMonoid_242 ~v0 ~v1 v2 = du_'42''45'isMonoid_242 v2
du_'42''45'isMonoid_242 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
du_'42''45'isMonoid_242 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1568
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.*-isSemigroup
d_'42''45'isSemigroup_244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_'42''45'isSemigroup_244 ~v0 ~v1 v2
  = du_'42''45'isSemigroup_244 v2
du_'42''45'isSemigroup_244 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
du_'42''45'isSemigroup_244 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1566
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.assoc
d_assoc_246 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_246 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_assoc_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_744
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                     (coe
                        d_isCommutativeSemiring_62
                        (coe d_isAlmostCommutativeRing_214 (coe v0))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.comm
d_comm_248 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_248 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_comm_746
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
               (coe
                  d_isCommutativeSemiring_62
                  (coe d_isAlmostCommutativeRing_214 (coe v0))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.∙-cong
d_'8729''45'cong_250 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_250 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_478
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_744
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                        (coe
                           d_isCommutativeSemiring_62
                           (coe d_isAlmostCommutativeRing_214 (coe v0)))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.∙-congʳ
d_'8729''45'cong'691'_252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_252 ~v0 ~v1 v2
  = du_'8729''45'cong'691'_252 v2
du_'8729''45'cong'691'_252 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_252 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v6) in
                      coe
                        (let v8 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v7) in
                         coe
                           (let v9
                                  = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v8) in
                            coe
                              (let v10
                                     = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                         (coe v8) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                                    (coe v10)
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                          (coe v9)))))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.∙-congˡ
d_'8729''45'cong'737'_254 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_254 ~v0 ~v1 v2
  = du_'8729''45'cong'737'_254 v2
du_'8729''45'cong'737'_254 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_254 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v6) in
                      coe
                        (let v8 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v7) in
                         coe
                           (let v9
                                  = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v8) in
                            coe
                              (let v10
                                     = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                         (coe v8) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                                    (coe v10)
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                          (coe v9)))))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.identity
d_identity_256 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_256 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_696
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_744
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                  (coe
                     d_isCommutativeSemiring_62
                     (coe d_isAlmostCommutativeRing_214 (coe v0)))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.identityʳ
d_identity'691'_258 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
d_identity'691'_258 ~v0 ~v1 v2 = du_identity'691'_258 v2
du_identity'691'_258 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
du_identity'691'_258 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_identity'691'_726
                     (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v5)))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.identityˡ
d_identity'737'_260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
d_identity'737'_260 ~v0 ~v1 v2 = du_identity'737'_260 v2
du_identity'737'_260 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
du_identity'737'_260 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_identity'737'_724
                     (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v5)))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.isCommutativeMagma
d_isCommutativeMagma_262 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
d_isCommutativeMagma_262 ~v0 ~v1 v2 = du_isCommutativeMagma_262 v2
du_isCommutativeMagma_262 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
du_isCommutativeMagma_262 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_584
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_784
                        (coe v5)))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_264 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
d_'43''45'isCommutativeMonoid_264 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
            (coe
               d_isCommutativeSemiring_62
               (coe d_isAlmostCommutativeRing_214 (coe v0)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.isCommutativeSemigroup
d_isCommutativeSemigroup_266 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
d_isCommutativeSemigroup_266 ~v0 ~v1 v2
  = du_isCommutativeSemigroup_266 v2
du_isCommutativeSemigroup_266 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
du_isCommutativeSemigroup_266 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_784
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                     (coe v4))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.isMagma
d_isMagma_268 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_268 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_478
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_744
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                     (coe
                        d_isCommutativeSemiring_62
                        (coe d_isAlmostCommutativeRing_214 (coe v0))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.isMonoid
d_isMonoid_270 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
d_isMonoid_270 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_744
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
               (coe
                  d_isCommutativeSemiring_62
                  (coe d_isAlmostCommutativeRing_214 (coe v0))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.isSemigroup
d_isSemigroup_272 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_isSemigroup_272 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_744
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                  (coe
                     d_isCommutativeSemiring_62
                     (coe d_isAlmostCommutativeRing_214 (coe v0)))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.isUnitalMagma
d_isUnitalMagma_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_640
d_isUnitalMagma_274 ~v0 ~v1 v2 = du_isUnitalMagma_274 v2
du_isUnitalMagma_274 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_640
du_isUnitalMagma_274 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_728
                     (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v5)))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.-‿*-distribˡ
d_'45''8255''42''45'distrib'737'_276 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny -> AgdaAny
d_'45''8255''42''45'distrib'737'_276 v0
  = coe
      d_'45''8255''42''45'distrib'737'_70
      (coe d_isAlmostCommutativeRing_214 (coe v0))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.-‿+-comm
d_'45''8255''43''45'comm_278 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny -> AgdaAny
d_'45''8255''43''45'comm_278 v0
  = coe
      d_'45''8255''43''45'comm_76
      (coe d_isAlmostCommutativeRing_214 (coe v0))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.-‿cong
d_'45''8255'cong_280 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'45''8255'cong_280 v0
  = coe
      d_'45''8255'cong_64 (coe d_isAlmostCommutativeRing_214 (coe v0))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.distrib
d_distrib_282 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_282 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1514
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
            (coe
               d_isCommutativeSemiring_62
               (coe d_isAlmostCommutativeRing_214 (coe v0)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.distribʳ
d_distrib'691'_284 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_284 ~v0 ~v1 v2 = du_distrib'691'_284 v2
du_distrib'691'_284 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'691'_284 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_distrib'691'_1518
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.distribˡ
d_distrib'737'_286 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_286 ~v0 ~v1 v2 = du_distrib'737'_286 v2
du_distrib'737'_286 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'737'_286 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_distrib'737'_1516
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.isCommutativeSemiring
d_isCommutativeSemiring_288 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1696
d_isCommutativeSemiring_288 v0
  = coe
      d_isCommutativeSemiring_62
      (coe d_isAlmostCommutativeRing_214 (coe v0))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.isCommutativeSemiringWithoutOne
d_isCommutativeSemiringWithoutOne_290 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1390
d_isCommutativeSemiringWithoutOne_290 ~v0 ~v1 v2
  = du_isCommutativeSemiringWithoutOne_290 v2
du_isCommutativeSemiringWithoutOne_290 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1390
du_isCommutativeSemiringWithoutOne_290 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1798
         (coe d_isCommutativeSemiring_62 (coe v1)))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.isEquivalence
d_isEquivalence_292 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_292 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_478
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_744
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                        (coe
                           d_isCommutativeSemiring_62
                           (coe d_isAlmostCommutativeRing_214 (coe v0)))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.isNearSemiring
d_isNearSemiring_294 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1216
d_isNearSemiring_294 ~v0 ~v1 v2 = du_isNearSemiring_294 v2
du_isNearSemiring_294 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1216
du_isNearSemiring_294 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_isNearSemiring_1382
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1678
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.isPartialEquivalence
d_isPartialEquivalence_296 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_296 ~v0 ~v1 v2
  = du_isPartialEquivalence_296 v2
du_isPartialEquivalence_296 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_296 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v6) in
                      coe
                        (let v8 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v7) in
                         coe
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                 (coe v8))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.isSemiring
d_isSemiring_298 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1588
d_isSemiring_298 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
      (coe
         d_isCommutativeSemiring_62
         (coe d_isAlmostCommutativeRing_214 (coe v0)))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_300 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1486
d_isSemiringWithoutAnnihilatingZero_300 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
         (coe
            d_isCommutativeSemiring_62
            (coe d_isAlmostCommutativeRing_214 (coe v0))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.isSemiringWithoutOne
d_isSemiringWithoutOne_302 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1296
d_isSemiringWithoutOne_302 ~v0 ~v1 v2
  = du_isSemiringWithoutOne_302 v2
du_isSemiringWithoutOne_302 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1296
du_isSemiringWithoutOne_302 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1678
            (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.refl
d_refl_304 :: T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
d_refl_304 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_478
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                           (coe
                              d_isCommutativeSemiring_62
                              (coe d_isAlmostCommutativeRing_214 (coe v0))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.reflexive
d_reflexive_306 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_306 ~v0 ~v1 v2 = du_reflexive_306 v2
du_reflexive_306 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_306 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v6) in
                      coe
                        (let v8 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v7) in
                         coe
                           (\ v9 v10 v11 ->
                              coe
                                MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                                (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v8))
                                v9))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.setoid
d_setoid_308 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_308 ~v0 ~v1 v2 = du_setoid_308 v2
du_setoid_308 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_308 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v6) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_setoid_200
                           (coe MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v7)))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.sym
d_sym_310 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_310 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_478
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                           (coe
                              d_isCommutativeSemiring_62
                              (coe d_isAlmostCommutativeRing_214 (coe v0))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.trans
d_trans_312 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_312 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_478
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                           (coe
                              d_isCommutativeSemiring_62
                              (coe d_isAlmostCommutativeRing_214 (coe v0))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.zero
d_zero_314 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_314 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_1604
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
         (coe
            d_isCommutativeSemiring_62
            (coe d_isAlmostCommutativeRing_214 (coe v0))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.zeroʳ
d_zero'691'_316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
d_zero'691'_316 ~v0 ~v1 v2 = du_zero'691'_316 v2
du_zero'691'_316 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
du_zero'691'_316 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_zero'691'_1380
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1678
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.zeroˡ
d_zero'737'_318 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
d_zero'737'_318 ~v0 ~v1 v2 = du_zero'737'_318 v2
du_zero'737'_318 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
du_zero'737'_318 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_zero'737'_1378
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1678
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing.commutativeSemiring
d_commutativeSemiring_320 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemiring_2470
d_commutativeSemiring_320 ~v0 ~v1 v2
  = du_commutativeSemiring_320 v2
du_commutativeSemiring_320 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemiring_2470
du_commutativeSemiring_320 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeSemiring'46'constructor_45179
      (d__'43'__204 (coe v0)) (d__'42'__206 (coe v0))
      (d_0'35'_210 (coe v0)) (d_1'35'_212 (coe v0))
      (d_isCommutativeSemiring_62
         (coe d_isAlmostCommutativeRing_214 (coe v0)))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.*-commutativeMonoid
d_'42''45'commutativeMonoid_324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_966
d_'42''45'commutativeMonoid_324 ~v0 ~v1 v2
  = du_'42''45'commutativeMonoid_324 v2
du_'42''45'commutativeMonoid_324 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_966
du_'42''45'commutativeMonoid_324 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.du_'42''45'commutativeMonoid_2642
      (coe du_commutativeSemiring_320 (coe v0))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.commutativeSemigroup
d_commutativeSemigroup_326 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_666
d_commutativeSemigroup_326 ~v0 ~v1 v2
  = du_commutativeSemigroup_326 v2
du_commutativeSemigroup_326 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_666
du_commutativeSemigroup_326 v0
  = let v1 = coe du_commutativeSemiring_320 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Bundles.du_commutativeSemigroup_1052
         (coe
            MAlonzo.Code.Algebra.Bundles.du_'42''45'commutativeMonoid_2642
            (coe v1)))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.magma
d_magma_328 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_72
d_magma_328 ~v0 ~v1 v2 = du_magma_328 v2
du_magma_328 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_72
du_magma_328 v0
  = let v1 = coe du_commutativeSemiring_320 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_semiring_2600 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
                    (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Bundles.du_'42''45'monoid_2288 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Bundles.du_magma_588
                  (coe MAlonzo.Code.Algebra.Bundles.du_semigroup_948 (coe v4))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.*-monoid
d_'42''45'monoid_330 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886
d_'42''45'monoid_330 ~v0 ~v1 v2 = du_'42''45'monoid_330 v2
du_'42''45'monoid_330 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886
du_'42''45'monoid_330 v0
  = let v1 = coe du_commutativeSemiring_320 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_semiring_2600 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Bundles.du_'42''45'monoid_2288
            (coe
               MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
               (coe v2))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.semigroup
d_semigroup_332 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_540
d_semigroup_332 ~v0 ~v1 v2 = du_semigroup_332 v2
du_semigroup_332 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_540
du_semigroup_332 v0
  = let v1 = coe du_commutativeSemiring_320 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_semiring_2600 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Bundles.du_semigroup_948
               (coe
                  MAlonzo.Code.Algebra.Bundles.du_'42''45'monoid_2288 (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.+-commutativeMonoid
d_'43''45'commutativeMonoid_334 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_966
d_'43''45'commutativeMonoid_334 ~v0 ~v1 v2
  = du_'43''45'commutativeMonoid_334 v2
du_'43''45'commutativeMonoid_334 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_966
du_'43''45'commutativeMonoid_334 v0
  = let v1 = coe du_commutativeSemiring_320 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_semiring_2600 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Bundles.du_'43''45'commutativeMonoid_2266
            (coe
               MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
               (coe v2))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.magma
d_magma_336 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_72
d_magma_336 ~v0 ~v1 v2 = du_magma_336 v2
du_magma_336 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_72
du_magma_336 v0
  = let v1 = coe du_commutativeSemiring_320 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_semiring_2600 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
                    (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Bundles.du_'43''45'commutativeMonoid_2266
                       (coe v3) in
             coe
               (let v5
                      = coe MAlonzo.Code.Algebra.Bundles.du_monoid_1036 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Bundles.du_magma_588
                     (coe MAlonzo.Code.Algebra.Bundles.du_semigroup_948 (coe v5)))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.monoid
d_monoid_338 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886
d_monoid_338 ~v0 ~v1 v2 = du_monoid_338 v2
du_monoid_338 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886
du_monoid_338 v0
  = let v1 = coe du_commutativeSemiring_320 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_semiring_2600 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Bundles.du_monoid_1036
               (coe
                  MAlonzo.Code.Algebra.Bundles.du_'43''45'commutativeMonoid_2266
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.semigroup
d_semigroup_340 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_540
d_semigroup_340 ~v0 ~v1 v2 = du_semigroup_340 v2
du_semigroup_340 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_540
du_semigroup_340 v0
  = let v1 = coe du_commutativeSemiring_320 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_semiring_2600 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
                    (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Bundles.du_'43''45'commutativeMonoid_2266
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Bundles.du_semigroup_948
                  (coe MAlonzo.Code.Algebra.Bundles.du_monoid_1036 (coe v4))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing._.semiring
d_semiring_342 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Semiring_2304
d_semiring_342 ~v0 ~v1 v2 = du_semiring_342 v2
du_semiring_342 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Semiring_2304
du_semiring_342 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.du_semiring_2600
      (coe du_commutativeSemiring_320 (coe v0))
-- Algebra.Solver.Ring.AlmostCommutativeRing.AlmostCommutativeRing.rawRing
d_rawRing_344 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276
d_rawRing_344 ~v0 ~v1 v2 = du_rawRing_344 v2
du_rawRing_344 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276
du_rawRing_344 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_RawRing'46'constructor_3989
      (d__'43'__204 (coe v0)) (d__'42'__206 (coe v0))
      (d_'45'__208 (coe v0)) (d_0'35'_210 (coe v0))
      (d_1'35'_212 (coe v0))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_
d__'45'Raw'45'AlmostCommutative'10230'__358 a0 a1 a2 a3 a4 a5 = ()
data T__'45'Raw'45'AlmostCommutative'10230'__358
  = C__'45'Raw'45'AlmostCommutative'10230'_'46'constructor_9475 (AgdaAny ->
                                                                 AgdaAny)
                                                                (AgdaAny -> AgdaAny -> AgdaAny)
                                                                (AgdaAny -> AgdaAny -> AgdaAny)
                                                                (AgdaAny -> AgdaAny) AgdaAny AgdaAny
-- Algebra.Solver.Ring.AlmostCommutativeRing.F._*_
d__'42'__374 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny -> AgdaAny
d__'42'__374 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du__'42'__374 v4
du__'42'__374 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'42'__374 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing.F._+_
d__'43'__376 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny -> AgdaAny
d__'43'__376 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du__'43'__376 v4
du__'43'__376 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'43'__376 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing.F.-_
d_'45'__392 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
d_'45'__392 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_'45'__392 v4
du_'45'__392 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  AgdaAny -> AgdaAny
du_'45'__392 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing.F.0#
d_0'35'_394 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 -> AgdaAny
d_0'35'_394 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_0'35'_394 v4
du_0'35'_394 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 -> AgdaAny
du_0'35'_394 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing.F.1#
d_1'35'_396 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 -> AgdaAny
d_1'35'_396 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_1'35'_396 v4
du_1'35'_396 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 -> AgdaAny
du_1'35'_396 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d_1'35'_308 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing.F.Carrier
d_Carrier_398 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 -> ()
d_Carrier_398 = erased
-- Algebra.Solver.Ring.AlmostCommutativeRing.T._*_
d__'42'__406 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny -> AgdaAny
d__'42'__406 v0 = coe d__'42'__206 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing.T._+_
d__'43'__408 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny -> AgdaAny
d__'43'__408 v0 = coe d__'43'__204 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing.T._≈_
d__'8776'__410 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny -> ()
d__'8776'__410 = erased
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.*-assoc
d_'42''45'assoc_412 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_412 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'assoc_1510
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
            (coe
               d_isCommutativeSemiring_62
               (coe d_isAlmostCommutativeRing_214 (coe v0)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.*-comm
d_'42''45'comm_414 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'comm_414 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'comm_1712
      (coe
         d_isCommutativeSemiring_62
         (coe d_isAlmostCommutativeRing_214 (coe v0)))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.*-commutativeMonoid
d_'42''45'commutativeMonoid_416 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_966
d_'42''45'commutativeMonoid_416 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'42''45'commutativeMonoid_416 v5
du_'42''45'commutativeMonoid_416 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_966
du_'42''45'commutativeMonoid_416 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.du_'42''45'commutativeMonoid_2642
      (coe du_commutativeSemiring_320 (coe v0))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.commutativeSemigroup
d_commutativeSemigroup_418 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_666
d_commutativeSemigroup_418 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_commutativeSemigroup_418 v5
du_commutativeSemigroup_418 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_666
du_commutativeSemigroup_418 v0
  = let v1 = coe du_commutativeSemiring_320 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Bundles.du_commutativeSemigroup_1052
         (coe
            MAlonzo.Code.Algebra.Bundles.du_'42''45'commutativeMonoid_2642
            (coe v1)))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.*-cong
d_'42''45'cong_420 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_420 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'cong_1508
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
            (coe
               d_isCommutativeSemiring_62
               (coe d_isAlmostCommutativeRing_214 (coe v0)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.∙-congʳ
d_'8729''45'cong'691'_422 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_422 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'691'_422 v5
du_'8729''45'cong'691'_422 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_422 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = coe
                          MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1568
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v5) in
                   coe
                     (let v7 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v6) in
                      coe
                        (let v8
                               = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v7) in
                         coe
                           (let v9
                                  = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 (coe v7) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                                 (coe v9)
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                       (coe v8))))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.∙-congˡ
d_'8729''45'cong'737'_424 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_424 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'737'_424 v5
du_'8729''45'cong'737'_424 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_424 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = coe
                          MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1568
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v5) in
                   coe
                     (let v7 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v6) in
                      coe
                        (let v8
                               = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v7) in
                         coe
                           (let v9
                                  = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 (coe v7) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                                 (coe v9)
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                       (coe v8))))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.*-identity
d_'42''45'identity_426 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_426 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1512
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
            (coe
               d_isCommutativeSemiring_62
               (coe d_isAlmostCommutativeRing_214 (coe v0)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.identityʳ
d_identity'691'_428 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
d_identity'691'_428 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_identity'691'_428 v5
du_identity'691'_428 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
du_identity'691'_428 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_identity'691'_726
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1568
                     (coe v4))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.identityˡ
d_identity'737'_430 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
d_identity'737'_430 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_identity'737'_430 v5
du_identity'737'_430 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
du_identity'737'_430 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_identity'737'_724
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1568
                     (coe v4))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.isCommutativeMagma
d_isCommutativeMagma_432 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
d_isCommutativeMagma_432 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeMagma_432 v5
du_isCommutativeMagma_432 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
du_isCommutativeMagma_432 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1798
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_584
               (coe
                  MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1472
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.*-isCommutativeMonoid
d_'42''45'isCommutativeMonoid_434 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
d_'42''45'isCommutativeMonoid_434 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'42''45'isCommutativeMonoid_434 v5
du_'42''45'isCommutativeMonoid_434 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
du_'42''45'isCommutativeMonoid_434 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeMonoid_1806
         (coe d_isCommutativeSemiring_62 (coe v1)))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_436 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
d_'42''45'isCommutativeSemigroup_436 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'42''45'isCommutativeSemigroup_436 v5
du_'42''45'isCommutativeSemigroup_436 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
du_'42''45'isCommutativeSemigroup_436 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1472
            (coe
               MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1798
               (coe v2))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.*-isMagma
d_'42''45'isMagma_438 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'42''45'isMagma_438 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'42''45'isMagma_438 v5
du_'42''45'isMagma_438 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_'42''45'isMagma_438 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1564
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.*-isMonoid
d_'42''45'isMonoid_440 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
d_'42''45'isMonoid_440 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'42''45'isMonoid_440 v5
du_'42''45'isMonoid_440 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
du_'42''45'isMonoid_440 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1568
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.*-isSemigroup
d_'42''45'isSemigroup_442 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_'42''45'isSemigroup_442 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'42''45'isSemigroup_442 v5
du_'42''45'isSemigroup_442 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
du_'42''45'isSemigroup_442 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1566
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.magma
d_magma_444 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_72
d_magma_444 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_magma_444 v5
du_magma_444 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_72
du_magma_444 v0
  = let v1 = coe du_commutativeSemiring_320 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_semiring_2600 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
                    (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Bundles.du_'42''45'monoid_2288 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Bundles.du_magma_588
                  (coe MAlonzo.Code.Algebra.Bundles.du_semigroup_948 (coe v4))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.*-monoid
d_'42''45'monoid_446 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886
d_'42''45'monoid_446 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'42''45'monoid_446 v5
du_'42''45'monoid_446 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886
du_'42''45'monoid_446 v0
  = let v1 = coe du_commutativeSemiring_320 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_semiring_2600 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Bundles.du_'42''45'monoid_2288
            (coe
               MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
               (coe v2))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.semigroup
d_semigroup_448 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_540
d_semigroup_448 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_semigroup_448 v5
du_semigroup_448 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_540
du_semigroup_448 v0
  = let v1 = coe du_commutativeSemiring_320 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_semiring_2600 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Bundles.du_semigroup_948
               (coe
                  MAlonzo.Code.Algebra.Bundles.du_'42''45'monoid_2288 (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.assoc
d_assoc_450 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_450 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_assoc_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_744
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                     (coe
                        d_isCommutativeSemiring_62
                        (coe d_isAlmostCommutativeRing_214 (coe v0))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.comm
d_comm_452 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_452 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_comm_746
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
               (coe
                  d_isCommutativeSemiring_62
                  (coe d_isAlmostCommutativeRing_214 (coe v0))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.+-commutativeMonoid
d_'43''45'commutativeMonoid_454 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_966
d_'43''45'commutativeMonoid_454 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'43''45'commutativeMonoid_454 v5
du_'43''45'commutativeMonoid_454 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_966
du_'43''45'commutativeMonoid_454 v0
  = let v1 = coe du_commutativeSemiring_320 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_semiring_2600 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Bundles.du_'43''45'commutativeMonoid_2266
            (coe
               MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
               (coe v2))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.∙-cong
d_'8729''45'cong_456 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_456 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_478
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_744
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                        (coe
                           d_isCommutativeSemiring_62
                           (coe d_isAlmostCommutativeRing_214 (coe v0)))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.∙-congʳ
d_'8729''45'cong'691'_458 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_458 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'691'_458 v5
du_'8729''45'cong'691'_458 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_458 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v6) in
                      coe
                        (let v8 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v7) in
                         coe
                           (let v9
                                  = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v8) in
                            coe
                              (let v10
                                     = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                         (coe v8) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                                    (coe v10)
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                          (coe v9)))))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.∙-congˡ
d_'8729''45'cong'737'_460 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_460 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'737'_460 v5
du_'8729''45'cong'737'_460 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_460 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v6) in
                      coe
                        (let v8 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v7) in
                         coe
                           (let v9
                                  = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v8) in
                            coe
                              (let v10
                                     = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                         (coe v8) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                                    (coe v10)
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                          (coe v9)))))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.identity
d_identity_462 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_462 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_696
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_744
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                  (coe
                     d_isCommutativeSemiring_62
                     (coe d_isAlmostCommutativeRing_214 (coe v0)))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.identityʳ
d_identity'691'_464 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
d_identity'691'_464 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_identity'691'_464 v5
du_identity'691'_464 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
du_identity'691'_464 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_identity'691'_726
                     (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v5)))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.identityˡ
d_identity'737'_466 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
d_identity'737'_466 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_identity'737'_466 v5
du_identity'737'_466 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
du_identity'737'_466 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_identity'737'_724
                     (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v5)))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.isCommutativeMagma
d_isCommutativeMagma_468 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
d_isCommutativeMagma_468 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeMagma_468 v5
du_isCommutativeMagma_468 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
du_isCommutativeMagma_468 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_584
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_784
                        (coe v5)))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_470 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
d_'43''45'isCommutativeMonoid_470 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
            (coe
               d_isCommutativeSemiring_62
               (coe d_isAlmostCommutativeRing_214 (coe v0)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.isCommutativeSemigroup
d_isCommutativeSemigroup_472 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
d_isCommutativeSemigroup_472 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeSemigroup_472 v5
du_isCommutativeSemigroup_472 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
du_isCommutativeSemigroup_472 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_784
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                     (coe v4))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.isMagma
d_isMagma_474 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_474 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_478
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_744
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                     (coe
                        d_isCommutativeSemiring_62
                        (coe d_isAlmostCommutativeRing_214 (coe v0))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.isMonoid
d_isMonoid_476 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
d_isMonoid_476 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_744
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
               (coe
                  d_isCommutativeSemiring_62
                  (coe d_isAlmostCommutativeRing_214 (coe v0))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.isSemigroup
d_isSemigroup_478 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_isSemigroup_478 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_744
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                  (coe
                     d_isCommutativeSemiring_62
                     (coe d_isAlmostCommutativeRing_214 (coe v0)))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.isUnitalMagma
d_isUnitalMagma_480 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_640
d_isUnitalMagma_480 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isUnitalMagma_480 v5
du_isUnitalMagma_480 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_640
du_isUnitalMagma_480 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_728
                     (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v5)))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.magma
d_magma_482 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_72
d_magma_482 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_magma_482 v5
du_magma_482 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_72
du_magma_482 v0
  = let v1 = coe du_commutativeSemiring_320 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_semiring_2600 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
                    (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Bundles.du_'43''45'commutativeMonoid_2266
                       (coe v3) in
             coe
               (let v5
                      = coe MAlonzo.Code.Algebra.Bundles.du_monoid_1036 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Bundles.du_magma_588
                     (coe MAlonzo.Code.Algebra.Bundles.du_semigroup_948 (coe v5)))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.monoid
d_monoid_484 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886
d_monoid_484 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_monoid_484 v5
du_monoid_484 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886
du_monoid_484 v0
  = let v1 = coe du_commutativeSemiring_320 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_semiring_2600 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Bundles.du_monoid_1036
               (coe
                  MAlonzo.Code.Algebra.Bundles.du_'43''45'commutativeMonoid_2266
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.semigroup
d_semigroup_486 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_540
d_semigroup_486 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_semigroup_486 v5
du_semigroup_486 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_540
du_semigroup_486 v0
  = let v1 = coe du_commutativeSemiring_320 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_semiring_2600 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
                    (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Bundles.du_'43''45'commutativeMonoid_2266
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Bundles.du_semigroup_948
                  (coe MAlonzo.Code.Algebra.Bundles.du_monoid_1036 (coe v4))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.-_
d_'45'__488 :: T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
d_'45'__488 v0 = coe d_'45'__208 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.-‿*-distribˡ
d_'45''8255''42''45'distrib'737'_490 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny -> AgdaAny
d_'45''8255''42''45'distrib'737'_490 v0
  = coe
      d_'45''8255''42''45'distrib'737'_70
      (coe d_isAlmostCommutativeRing_214 (coe v0))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.-‿+-comm
d_'45''8255''43''45'comm_492 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny -> AgdaAny
d_'45''8255''43''45'comm_492 v0
  = coe
      d_'45''8255''43''45'comm_76
      (coe d_isAlmostCommutativeRing_214 (coe v0))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.-‿cong
d_'45''8255'cong_494 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'45''8255'cong_494 v0
  = coe
      d_'45''8255'cong_64 (coe d_isAlmostCommutativeRing_214 (coe v0))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.0#
d_0'35'_496 :: T_AlmostCommutativeRing_178 -> AgdaAny
d_0'35'_496 v0 = coe d_0'35'_210 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.1#
d_1'35'_498 :: T_AlmostCommutativeRing_178 -> AgdaAny
d_1'35'_498 v0 = coe d_1'35'_212 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.Carrier
d_Carrier_500 :: T_AlmostCommutativeRing_178 -> ()
d_Carrier_500 = erased
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.commutativeSemiring
d_commutativeSemiring_502 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemiring_2470
d_commutativeSemiring_502 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_commutativeSemiring_502 v5
du_commutativeSemiring_502 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemiring_2470
du_commutativeSemiring_502 v0
  = coe du_commutativeSemiring_320 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.distrib
d_distrib_504 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_504 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1514
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
            (coe
               d_isCommutativeSemiring_62
               (coe d_isAlmostCommutativeRing_214 (coe v0)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.distribʳ
d_distrib'691'_506 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_506 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_distrib'691'_506 v5
du_distrib'691'_506 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'691'_506 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_distrib'691'_1518
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.distribˡ
d_distrib'737'_508 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_508 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_distrib'737'_508 v5
du_distrib'737'_508 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'737'_508 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_distrib'737'_1516
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.isAlmostCommutativeRing
d_isAlmostCommutativeRing_510 ::
  T_AlmostCommutativeRing_178 -> T_IsAlmostCommutativeRing_26
d_isAlmostCommutativeRing_510 v0
  = coe d_isAlmostCommutativeRing_214 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.isCommutativeSemiring
d_isCommutativeSemiring_512 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1696
d_isCommutativeSemiring_512 v0
  = coe
      d_isCommutativeSemiring_62
      (coe d_isAlmostCommutativeRing_214 (coe v0))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.isCommutativeSemiringWithoutOne
d_isCommutativeSemiringWithoutOne_514 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1390
d_isCommutativeSemiringWithoutOne_514 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeSemiringWithoutOne_514 v5
du_isCommutativeSemiringWithoutOne_514 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1390
du_isCommutativeSemiringWithoutOne_514 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1798
         (coe d_isCommutativeSemiring_62 (coe v1)))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.isEquivalence
d_isEquivalence_516 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_516 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_478
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_744
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                        (coe
                           d_isCommutativeSemiring_62
                           (coe d_isAlmostCommutativeRing_214 (coe v0)))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.isNearSemiring
d_isNearSemiring_518 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1216
d_isNearSemiring_518 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isNearSemiring_518 v5
du_isNearSemiring_518 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1216
du_isNearSemiring_518 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_isNearSemiring_1382
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1678
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.isPartialEquivalence
d_isPartialEquivalence_520 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_520 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_520 v5
du_isPartialEquivalence_520 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_520 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v6) in
                      coe
                        (let v8 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v7) in
                         coe
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                 (coe v8))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.isSemiring
d_isSemiring_522 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1588
d_isSemiring_522 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
      (coe
         d_isCommutativeSemiring_62
         (coe d_isAlmostCommutativeRing_214 (coe v0)))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_524 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1486
d_isSemiringWithoutAnnihilatingZero_524 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
         (coe
            d_isCommutativeSemiring_62
            (coe d_isAlmostCommutativeRing_214 (coe v0))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.isSemiringWithoutOne
d_isSemiringWithoutOne_526 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1296
d_isSemiringWithoutOne_526 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isSemiringWithoutOne_526 v5
du_isSemiringWithoutOne_526 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1296
du_isSemiringWithoutOne_526 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1678
            (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.rawRing
d_rawRing_528 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276
d_rawRing_528 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_rawRing_528 v5
du_rawRing_528 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276
du_rawRing_528 v0 = coe du_rawRing_344 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.refl
d_refl_530 :: T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
d_refl_530 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_478
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                           (coe
                              d_isCommutativeSemiring_62
                              (coe d_isAlmostCommutativeRing_214 (coe v0))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.reflexive
d_reflexive_532 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_532 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_532 v5
du_reflexive_532 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_532 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v6) in
                      coe
                        (let v8 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v7) in
                         coe
                           (\ v9 v10 v11 ->
                              coe
                                MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                                (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v8))
                                v9))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.semiring
d_semiring_534 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Semiring_2304
d_semiring_534 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_semiring_534 v5
du_semiring_534 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Semiring_2304
du_semiring_534 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.du_semiring_2600
      (coe du_commutativeSemiring_320 (coe v0))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.setoid
d_setoid_536 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_536 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_536 v5
du_setoid_536 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_536 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v6) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_setoid_200
                           (coe MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v7)))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.sym
d_sym_538 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_538 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_478
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                           (coe
                              d_isCommutativeSemiring_62
                              (coe d_isAlmostCommutativeRing_214 (coe v0))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.trans
d_trans_540 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_540 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_478
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                           (coe
                              d_isCommutativeSemiring_62
                              (coe d_isAlmostCommutativeRing_214 (coe v0))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.zero
d_zero_542 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_542 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_1604
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
         (coe
            d_isCommutativeSemiring_62
            (coe d_isAlmostCommutativeRing_214 (coe v0))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.zeroʳ
d_zero'691'_544 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
d_zero'691'_544 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_zero'691'_544 v5
du_zero'691'_544 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
du_zero'691'_544 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_zero'691'_1380
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1678
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.T.zeroˡ
d_zero'737'_546 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
d_zero'737'_546 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_zero'737'_546 v5
du_zero'737'_546 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
du_zero'737'_546 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_zero'737'_1378
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1678
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._.Homomorphic₀
d_Homomorphic'8320'_550 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> ()
d_Homomorphic'8320'_550 = erased
-- Algebra.Solver.Ring.AlmostCommutativeRing._.Homomorphic₁
d_Homomorphic'8321'_552 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8321'_552 = erased
-- Algebra.Solver.Ring.AlmostCommutativeRing._.Homomorphic₂
d_Homomorphic'8322'_554 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8322'_554 = erased
-- Algebra.Solver.Ring.AlmostCommutativeRing._.Morphism
d_Morphism_556 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 -> ()
d_Morphism_556 = erased
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T._*_
d__'42'__604 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'42'__604 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du__'42'__604 v5
du__'42'__604 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny -> AgdaAny
du__'42'__604 v0 = coe d__'42'__206 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T._+_
d__'43'__606 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'43'__606 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du__'43'__606 v5
du__'43'__606 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny -> AgdaAny
du__'43'__606 v0 = coe d__'43'__204 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T._≈_
d__'8776'__608 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__608 = erased
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.*-assoc
d_'42''45'assoc_610 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_610 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_'42''45'assoc_610 v5
du_'42''45'assoc_610 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'42''45'assoc_610 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'assoc_1510
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
            (coe
               d_isCommutativeSemiring_62
               (coe d_isAlmostCommutativeRing_214 (coe v0)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.*-comm
d_'42''45'comm_612 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'comm_612 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_'42''45'comm_612 v5
du_'42''45'comm_612 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny -> AgdaAny
du_'42''45'comm_612 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'comm_1712
      (coe
         d_isCommutativeSemiring_62
         (coe d_isAlmostCommutativeRing_214 (coe v0)))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.*-commutativeMonoid
d_'42''45'commutativeMonoid_614 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_966
d_'42''45'commutativeMonoid_614 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_'42''45'commutativeMonoid_614 v5
du_'42''45'commutativeMonoid_614 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_966
du_'42''45'commutativeMonoid_614 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.du_'42''45'commutativeMonoid_2642
      (coe du_commutativeSemiring_320 (coe v0))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.commutativeSemigroup
d_commutativeSemigroup_616 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_666
d_commutativeSemigroup_616 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_commutativeSemigroup_616 v5
du_commutativeSemigroup_616 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_666
du_commutativeSemigroup_616 v0
  = let v1 = coe du_commutativeSemiring_320 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Bundles.du_commutativeSemigroup_1052
         (coe
            MAlonzo.Code.Algebra.Bundles.du_'42''45'commutativeMonoid_2642
            (coe v1)))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.*-cong
d_'42''45'cong_618 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_618 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_'42''45'cong_618 v5
du_'42''45'cong_618 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'42''45'cong_618 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'cong_1508
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
            (coe
               d_isCommutativeSemiring_62
               (coe d_isAlmostCommutativeRing_214 (coe v0)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.∙-congʳ
d_'8729''45'cong'691'_620 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_620 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_'8729''45'cong'691'_620 v5
du_'8729''45'cong'691'_620 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_620 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = coe
                          MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1568
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v5) in
                   coe
                     (let v7 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v6) in
                      coe
                        (let v8
                               = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v7) in
                         coe
                           (let v9
                                  = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 (coe v7) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                                 (coe v9)
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                       (coe v8))))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.∙-congˡ
d_'8729''45'cong'737'_622 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_622 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_'8729''45'cong'737'_622 v5
du_'8729''45'cong'737'_622 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_622 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = coe
                          MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1568
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v5) in
                   coe
                     (let v7 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v6) in
                      coe
                        (let v8
                               = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v7) in
                         coe
                           (let v9
                                  = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 (coe v7) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                                 (coe v9)
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                       (coe v8))))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.*-identity
d_'42''45'identity_624 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_624 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_'42''45'identity_624 v5
du_'42''45'identity_624 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'42''45'identity_624 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1512
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
            (coe
               d_isCommutativeSemiring_62
               (coe d_isAlmostCommutativeRing_214 (coe v0)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.identityʳ
d_identity'691'_626 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 -> AgdaAny -> AgdaAny
d_identity'691'_626 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_identity'691'_626 v5
du_identity'691'_626 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
du_identity'691'_626 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_identity'691'_726
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1568
                     (coe v4))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.identityˡ
d_identity'737'_628 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 -> AgdaAny -> AgdaAny
d_identity'737'_628 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_identity'737'_628 v5
du_identity'737'_628 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
du_identity'737'_628 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_identity'737'_724
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1568
                     (coe v4))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.isCommutativeMagma
d_isCommutativeMagma_630 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
d_isCommutativeMagma_630 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_isCommutativeMagma_630 v5
du_isCommutativeMagma_630 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
du_isCommutativeMagma_630 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1798
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_584
               (coe
                  MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1472
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.*-isCommutativeMonoid
d_'42''45'isCommutativeMonoid_632 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
d_'42''45'isCommutativeMonoid_632 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_'42''45'isCommutativeMonoid_632 v5
du_'42''45'isCommutativeMonoid_632 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
du_'42''45'isCommutativeMonoid_632 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeMonoid_1806
         (coe d_isCommutativeSemiring_62 (coe v1)))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_634 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
d_'42''45'isCommutativeSemigroup_634 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_'42''45'isCommutativeSemigroup_634 v5
du_'42''45'isCommutativeSemigroup_634 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
du_'42''45'isCommutativeSemigroup_634 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1472
            (coe
               MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1798
               (coe v2))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.*-isMagma
d_'42''45'isMagma_636 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'42''45'isMagma_636 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_'42''45'isMagma_636 v5
du_'42''45'isMagma_636 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_'42''45'isMagma_636 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1564
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.*-isMonoid
d_'42''45'isMonoid_638 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
d_'42''45'isMonoid_638 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_'42''45'isMonoid_638 v5
du_'42''45'isMonoid_638 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
du_'42''45'isMonoid_638 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1568
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.*-isSemigroup
d_'42''45'isSemigroup_640 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_'42''45'isSemigroup_640 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_'42''45'isSemigroup_640 v5
du_'42''45'isSemigroup_640 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
du_'42''45'isSemigroup_640 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1566
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.magma
d_magma_642 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_72
d_magma_642 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_magma_642 v5
du_magma_642 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_72
du_magma_642 v0
  = let v1 = coe du_commutativeSemiring_320 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_semiring_2600 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
                    (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Bundles.du_'42''45'monoid_2288 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Bundles.du_magma_588
                  (coe MAlonzo.Code.Algebra.Bundles.du_semigroup_948 (coe v4))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.*-monoid
d_'42''45'monoid_644 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886
d_'42''45'monoid_644 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_'42''45'monoid_644 v5
du_'42''45'monoid_644 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886
du_'42''45'monoid_644 v0
  = let v1 = coe du_commutativeSemiring_320 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_semiring_2600 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Bundles.du_'42''45'monoid_2288
            (coe
               MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
               (coe v2))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.semigroup
d_semigroup_646 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_540
d_semigroup_646 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_semigroup_646 v5
du_semigroup_646 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_540
du_semigroup_646 v0
  = let v1 = coe du_commutativeSemiring_320 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_semiring_2600 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Bundles.du_semigroup_948
               (coe
                  MAlonzo.Code.Algebra.Bundles.du_'42''45'monoid_2288 (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.assoc
d_assoc_648 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_648 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_assoc_648 v5
du_assoc_648 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_assoc_648 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_assoc_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_744
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                     (coe
                        d_isCommutativeSemiring_62
                        (coe d_isAlmostCommutativeRing_214 (coe v0))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.comm
d_comm_650 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_comm_650 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_comm_650 v5
du_comm_650 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny -> AgdaAny
du_comm_650 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_comm_746
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
               (coe
                  d_isCommutativeSemiring_62
                  (coe d_isAlmostCommutativeRing_214 (coe v0))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.+-commutativeMonoid
d_'43''45'commutativeMonoid_652 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_966
d_'43''45'commutativeMonoid_652 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_'43''45'commutativeMonoid_652 v5
du_'43''45'commutativeMonoid_652 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_966
du_'43''45'commutativeMonoid_652 v0
  = let v1 = coe du_commutativeSemiring_320 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_semiring_2600 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Bundles.du_'43''45'commutativeMonoid_2266
            (coe
               MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
               (coe v2))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.∙-cong
d_'8729''45'cong_654 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_654 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_'8729''45'cong_654 v5
du_'8729''45'cong_654 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong_654 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_478
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_744
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                        (coe
                           d_isCommutativeSemiring_62
                           (coe d_isAlmostCommutativeRing_214 (coe v0)))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.∙-congʳ
d_'8729''45'cong'691'_656 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_656 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_'8729''45'cong'691'_656 v5
du_'8729''45'cong'691'_656 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_656 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v6) in
                      coe
                        (let v8 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v7) in
                         coe
                           (let v9
                                  = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v8) in
                            coe
                              (let v10
                                     = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                         (coe v8) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                                    (coe v10)
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                          (coe v9)))))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.∙-congˡ
d_'8729''45'cong'737'_658 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_658 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_'8729''45'cong'737'_658 v5
du_'8729''45'cong'737'_658 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_658 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v6) in
                      coe
                        (let v8 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v7) in
                         coe
                           (let v9
                                  = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v8) in
                            coe
                              (let v10
                                     = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                         (coe v8) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                                    (coe v10)
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                          (coe v9)))))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.identity
d_identity_660 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_660 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_identity_660 v5
du_identity_660 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_identity_660 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_696
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_744
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                  (coe
                     d_isCommutativeSemiring_62
                     (coe d_isAlmostCommutativeRing_214 (coe v0)))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.identityʳ
d_identity'691'_662 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 -> AgdaAny -> AgdaAny
d_identity'691'_662 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_identity'691'_662 v5
du_identity'691'_662 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
du_identity'691'_662 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_identity'691'_726
                     (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v5)))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.identityˡ
d_identity'737'_664 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 -> AgdaAny -> AgdaAny
d_identity'737'_664 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_identity'737'_664 v5
du_identity'737'_664 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
du_identity'737'_664 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_identity'737'_724
                     (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v5)))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.isCommutativeMagma
d_isCommutativeMagma_666 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
d_isCommutativeMagma_666 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_isCommutativeMagma_666 v5
du_isCommutativeMagma_666 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
du_isCommutativeMagma_666 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_584
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_784
                        (coe v5)))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_668 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
d_'43''45'isCommutativeMonoid_668 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_'43''45'isCommutativeMonoid_668 v5
du_'43''45'isCommutativeMonoid_668 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
du_'43''45'isCommutativeMonoid_668 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
            (coe
               d_isCommutativeSemiring_62
               (coe d_isAlmostCommutativeRing_214 (coe v0)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.isCommutativeSemigroup
d_isCommutativeSemigroup_670 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
d_isCommutativeSemigroup_670 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_isCommutativeSemigroup_670 v5
du_isCommutativeSemigroup_670 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
du_isCommutativeSemigroup_670 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_784
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                     (coe v4))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.isMagma
d_isMagma_672 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_672 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_isMagma_672 v5
du_isMagma_672 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_isMagma_672 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_478
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_744
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                     (coe
                        d_isCommutativeSemiring_62
                        (coe d_isAlmostCommutativeRing_214 (coe v0))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.isMonoid
d_isMonoid_674 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
d_isMonoid_674 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_isMonoid_674 v5
du_isMonoid_674 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
du_isMonoid_674 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_744
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
               (coe
                  d_isCommutativeSemiring_62
                  (coe d_isAlmostCommutativeRing_214 (coe v0))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.isSemigroup
d_isSemigroup_676 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_isSemigroup_676 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_isSemigroup_676 v5
du_isSemigroup_676 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
du_isSemigroup_676 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_744
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                  (coe
                     d_isCommutativeSemiring_62
                     (coe d_isAlmostCommutativeRing_214 (coe v0)))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.isUnitalMagma
d_isUnitalMagma_678 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_640
d_isUnitalMagma_678 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_isUnitalMagma_678 v5
du_isUnitalMagma_678 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_640
du_isUnitalMagma_678 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_728
                     (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v5)))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.magma
d_magma_680 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_72
d_magma_680 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_magma_680 v5
du_magma_680 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_72
du_magma_680 v0
  = let v1 = coe du_commutativeSemiring_320 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_semiring_2600 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
                    (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Bundles.du_'43''45'commutativeMonoid_2266
                       (coe v3) in
             coe
               (let v5
                      = coe MAlonzo.Code.Algebra.Bundles.du_monoid_1036 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Bundles.du_magma_588
                     (coe MAlonzo.Code.Algebra.Bundles.du_semigroup_948 (coe v5)))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.monoid
d_monoid_682 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886
d_monoid_682 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_monoid_682 v5
du_monoid_682 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886
du_monoid_682 v0
  = let v1 = coe du_commutativeSemiring_320 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_semiring_2600 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Bundles.du_monoid_1036
               (coe
                  MAlonzo.Code.Algebra.Bundles.du_'43''45'commutativeMonoid_2266
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.semigroup
d_semigroup_684 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_540
d_semigroup_684 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_semigroup_684 v5
du_semigroup_684 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_540
du_semigroup_684 v0
  = let v1 = coe du_commutativeSemiring_320 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_semiring_2600 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
                    (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Bundles.du_'43''45'commutativeMonoid_2266
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Bundles.du_semigroup_948
                  (coe MAlonzo.Code.Algebra.Bundles.du_monoid_1036 (coe v4))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.-_
d_'45'__686 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 -> AgdaAny -> AgdaAny
d_'45'__686 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_'45'__686 v5
du_'45'__686 :: T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
du_'45'__686 v0 = coe d_'45'__208 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.-‿*-distribˡ
d_'45''8255''42''45'distrib'737'_688 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'45''8255''42''45'distrib'737'_688 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_'45''8255''42''45'distrib'737'_688 v5
du_'45''8255''42''45'distrib'737'_688 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny -> AgdaAny
du_'45''8255''42''45'distrib'737'_688 v0
  = coe
      d_'45''8255''42''45'distrib'737'_70
      (coe d_isAlmostCommutativeRing_214 (coe v0))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.-‿+-comm
d_'45''8255''43''45'comm_690 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'45''8255''43''45'comm_690 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_'45''8255''43''45'comm_690 v5
du_'45''8255''43''45'comm_690 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny -> AgdaAny
du_'45''8255''43''45'comm_690 v0
  = coe
      d_'45''8255''43''45'comm_76
      (coe d_isAlmostCommutativeRing_214 (coe v0))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.-‿cong
d_'45''8255'cong_692 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'45''8255'cong_692 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_'45''8255'cong_692 v5
du_'45''8255'cong_692 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'45''8255'cong_692 v0
  = coe
      d_'45''8255'cong_64 (coe d_isAlmostCommutativeRing_214 (coe v0))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.0#
d_0'35'_694 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 -> AgdaAny
d_0'35'_694 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_0'35'_694 v5
du_0'35'_694 :: T_AlmostCommutativeRing_178 -> AgdaAny
du_0'35'_694 v0 = coe d_0'35'_210 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.1#
d_1'35'_696 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 -> AgdaAny
d_1'35'_696 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_1'35'_696 v5
du_1'35'_696 :: T_AlmostCommutativeRing_178 -> AgdaAny
du_1'35'_696 v0 = coe d_1'35'_212 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.Carrier
d_Carrier_698 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 -> ()
d_Carrier_698 = erased
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.commutativeSemiring
d_commutativeSemiring_700 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemiring_2470
d_commutativeSemiring_700 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_commutativeSemiring_700 v5
du_commutativeSemiring_700 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemiring_2470
du_commutativeSemiring_700 v0
  = coe du_commutativeSemiring_320 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.distrib
d_distrib_702 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_702 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_distrib_702 v5
du_distrib_702 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_distrib_702 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1514
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
            (coe
               d_isCommutativeSemiring_62
               (coe d_isAlmostCommutativeRing_214 (coe v0)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.distribʳ
d_distrib'691'_704 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_704 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_distrib'691'_704 v5
du_distrib'691'_704 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'691'_704 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_distrib'691'_1518
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.distribˡ
d_distrib'737'_706 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_706 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_distrib'737'_706 v5
du_distrib'737'_706 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'737'_706 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_distrib'737'_1516
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.isAlmostCommutativeRing
d_isAlmostCommutativeRing_708 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  T_IsAlmostCommutativeRing_26
d_isAlmostCommutativeRing_708 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_isAlmostCommutativeRing_708 v5
du_isAlmostCommutativeRing_708 ::
  T_AlmostCommutativeRing_178 -> T_IsAlmostCommutativeRing_26
du_isAlmostCommutativeRing_708 v0
  = coe d_isAlmostCommutativeRing_214 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.isCommutativeSemiring
d_isCommutativeSemiring_710 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1696
d_isCommutativeSemiring_710 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_isCommutativeSemiring_710 v5
du_isCommutativeSemiring_710 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1696
du_isCommutativeSemiring_710 v0
  = coe
      d_isCommutativeSemiring_62
      (coe d_isAlmostCommutativeRing_214 (coe v0))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.isCommutativeSemiringWithoutOne
d_isCommutativeSemiringWithoutOne_712 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1390
d_isCommutativeSemiringWithoutOne_712 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_isCommutativeSemiringWithoutOne_712 v5
du_isCommutativeSemiringWithoutOne_712 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1390
du_isCommutativeSemiringWithoutOne_712 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1798
         (coe d_isCommutativeSemiring_62 (coe v1)))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.isEquivalence
d_isEquivalence_714 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_714 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_isEquivalence_714 v5
du_isEquivalence_714 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_714 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_478
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_744
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                        (coe
                           d_isCommutativeSemiring_62
                           (coe d_isAlmostCommutativeRing_214 (coe v0)))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.isNearSemiring
d_isNearSemiring_716 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1216
d_isNearSemiring_716 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_isNearSemiring_716 v5
du_isNearSemiring_716 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1216
du_isNearSemiring_716 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_isNearSemiring_1382
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1678
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.isPartialEquivalence
d_isPartialEquivalence_718 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_718 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_isPartialEquivalence_718 v5
du_isPartialEquivalence_718 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_718 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v6) in
                      coe
                        (let v8 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v7) in
                         coe
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                 (coe v8))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.isSemiring
d_isSemiring_720 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1588
d_isSemiring_720 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_isSemiring_720 v5
du_isSemiring_720 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1588
du_isSemiring_720 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
      (coe
         d_isCommutativeSemiring_62
         (coe d_isAlmostCommutativeRing_214 (coe v0)))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_722 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1486
d_isSemiringWithoutAnnihilatingZero_722 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_isSemiringWithoutAnnihilatingZero_722 v5
du_isSemiringWithoutAnnihilatingZero_722 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1486
du_isSemiringWithoutAnnihilatingZero_722 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
         (coe
            d_isCommutativeSemiring_62
            (coe d_isAlmostCommutativeRing_214 (coe v0))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.isSemiringWithoutOne
d_isSemiringWithoutOne_724 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1296
d_isSemiringWithoutOne_724 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_isSemiringWithoutOne_724 v5
du_isSemiringWithoutOne_724 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1296
du_isSemiringWithoutOne_724 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1678
            (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.rawRing
d_rawRing_726 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276
d_rawRing_726 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_rawRing_726 v5
du_rawRing_726 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276
du_rawRing_726 v0 = coe du_rawRing_344 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.refl
d_refl_728 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 -> AgdaAny -> AgdaAny
d_refl_728 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_refl_728 v5
du_refl_728 :: T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
du_refl_728 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_478
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                           (coe
                              d_isCommutativeSemiring_62
                              (coe d_isAlmostCommutativeRing_214 (coe v0))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.reflexive
d_reflexive_730 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_730 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_reflexive_730 v5
du_reflexive_730 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_730 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v6) in
                      coe
                        (let v8 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v7) in
                         coe
                           (\ v9 v10 v11 ->
                              coe
                                MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                                (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v8))
                                v9))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.semiring
d_semiring_732 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  MAlonzo.Code.Algebra.Bundles.T_Semiring_2304
d_semiring_732 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_semiring_732 v5
du_semiring_732 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Semiring_2304
du_semiring_732 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.du_semiring_2600
      (coe du_commutativeSemiring_320 (coe v0))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.setoid
d_setoid_734 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_734 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_setoid_734 v5
du_setoid_734 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_734 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v6) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_setoid_200
                           (coe MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v7)))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.sym
d_sym_736 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_736 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_sym_736 v5
du_sym_736 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_736 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_478
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                           (coe
                              d_isCommutativeSemiring_62
                              (coe d_isAlmostCommutativeRing_214 (coe v0))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.trans
d_trans_738 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_738 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_trans_738 v5
du_trans_738 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_738 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_478
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                           (coe
                              d_isCommutativeSemiring_62
                              (coe d_isAlmostCommutativeRing_214 (coe v0))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.zero
d_zero_740 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_740 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_zero_740 v5
du_zero_740 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_zero_740 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_1604
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
         (coe
            d_isCommutativeSemiring_62
            (coe d_isAlmostCommutativeRing_214 (coe v0))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.zeroʳ
d_zero'691'_742 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 -> AgdaAny -> AgdaAny
d_zero'691'_742 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_zero'691'_742 v5
du_zero'691'_742 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
du_zero'691'_742 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_zero'691'_1380
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1678
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.T.zeroˡ
d_zero'737'_744 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 -> AgdaAny -> AgdaAny
d_zero'737'_744 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_zero'737'_744 v5
du_zero'737'_744 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
du_zero'737'_744 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_zero'737'_1378
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1678
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.⟦_⟧
d_'10214'_'10215'_756 ::
  T__'45'Raw'45'AlmostCommutative'10230'__358 -> AgdaAny -> AgdaAny
d_'10214'_'10215'_756 v0
  = case coe v0 of
      C__'45'Raw'45'AlmostCommutative'10230'_'46'constructor_9475 v1 v2 v3 v4 v5 v6
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.+-homo
d_'43''45'homo_758 ::
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'43''45'homo_758 v0
  = case coe v0 of
      C__'45'Raw'45'AlmostCommutative'10230'_'46'constructor_9475 v1 v2 v3 v4 v5 v6
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.*-homo
d_'42''45'homo_760 ::
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_760 v0
  = case coe v0 of
      C__'45'Raw'45'AlmostCommutative'10230'_'46'constructor_9475 v1 v2 v3 v4 v5 v6
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.-‿homo
d_'45''8255'homo_762 ::
  T__'45'Raw'45'AlmostCommutative'10230'__358 -> AgdaAny -> AgdaAny
d_'45''8255'homo_762 v0
  = case coe v0 of
      C__'45'Raw'45'AlmostCommutative'10230'_'46'constructor_9475 v1 v2 v3 v4 v5 v6
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.0-homo
d_0'45'homo_764 ::
  T__'45'Raw'45'AlmostCommutative'10230'__358 -> AgdaAny
d_0'45'homo_764 v0
  = case coe v0 of
      C__'45'Raw'45'AlmostCommutative'10230'_'46'constructor_9475 v1 v2 v3 v4 v5 v6
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring.AlmostCommutativeRing._-Raw-AlmostCommutative⟶_.1-homo
d_1'45'homo_766 ::
  T__'45'Raw'45'AlmostCommutative'10230'__358 -> AgdaAny
d_1'45'homo_766 v0
  = case coe v0 of
      C__'45'Raw'45'AlmostCommutative'10230'_'46'constructor_9475 v1 v2 v3 v4 v5 v6
        -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring.AlmostCommutativeRing.-raw-almostCommutative⟶
d_'45'raw'45'almostCommutative'10230'_774 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358
d_'45'raw'45'almostCommutative'10230'_774 ~v0 ~v1 v2
  = du_'45'raw'45'almostCommutative'10230'_774 v2
du_'45'raw'45'almostCommutative'10230'_774 ::
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358
du_'45'raw'45'almostCommutative'10230'_774 v0
  = coe
      C__'45'Raw'45'AlmostCommutative'10230'_'46'constructor_9475
      (coe (\ v1 -> v1))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_34
              (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                 (coe
                    MAlonzo.Code.Algebra.Structures.d_isMagma_478
                    (coe
                       MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                       (coe
                          MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                          (coe
                             MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                             (coe
                                MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                (coe
                                   MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                   (coe
                                      d_isCommutativeSemiring_62
                                      (coe d_isAlmostCommutativeRing_214 (coe v0))))))))))
              (let v3 = coe du_rawRing_344 (coe v0) in
               coe (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v3 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_34
              (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                 (coe
                    MAlonzo.Code.Algebra.Structures.d_isMagma_478
                    (coe
                       MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                       (coe
                          MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                          (coe
                             MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                             (coe
                                MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                (coe
                                   MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                   (coe
                                      d_isCommutativeSemiring_62
                                      (coe d_isAlmostCommutativeRing_214 (coe v0))))))))))
              (let v3 = coe du_rawRing_344 (coe v0) in
               coe (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v3 v1 v2))))
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_34
              (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                 (coe
                    MAlonzo.Code.Algebra.Structures.d_isMagma_478
                    (coe
                       MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                       (coe
                          MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                          (coe
                             MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                             (coe
                                MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                (coe
                                   MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                   (coe
                                      d_isCommutativeSemiring_62
                                      (coe d_isAlmostCommutativeRing_214 (coe v0))))))))))
              (let v2 = coe du_rawRing_344 (coe v0) in
               coe (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v2 v1))))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_478
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                              (coe
                                 d_isCommutativeSemiring_62
                                 (coe d_isAlmostCommutativeRing_214 (coe v0))))))))))
         (let v1 = coe du_rawRing_344 (coe v0) in
          coe (MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v1))))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_478
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                              (coe
                                 d_isCommutativeSemiring_62
                                 (coe d_isAlmostCommutativeRing_214 (coe v0))))))))))
         (let v1 = coe du_rawRing_344 (coe v0) in
          coe (MAlonzo.Code.Algebra.Bundles.Raw.d_1'35'_308 (coe v1))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._._*_
d__'42'__784 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny -> AgdaAny
d__'42'__784 v0 = coe d__'42'__206 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing._._._+_
d__'43'__786 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny -> AgdaAny
d__'43'__786 v0 = coe d__'43'__204 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing._._._≈_
d__'8776'__788 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny -> ()
d__'8776'__788 = erased
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.*-assoc
d_'42''45'assoc_790 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_790 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'assoc_1510
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
            (coe
               d_isCommutativeSemiring_62
               (coe d_isAlmostCommutativeRing_214 (coe v0)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.*-comm
d_'42''45'comm_792 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'comm_792 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'comm_1712
      (coe
         d_isCommutativeSemiring_62
         (coe d_isAlmostCommutativeRing_214 (coe v0)))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.*-commutativeMonoid
d_'42''45'commutativeMonoid_794 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_966
d_'42''45'commutativeMonoid_794 ~v0 ~v1 v2
  = du_'42''45'commutativeMonoid_794 v2
du_'42''45'commutativeMonoid_794 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_966
du_'42''45'commutativeMonoid_794 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.du_'42''45'commutativeMonoid_2642
      (coe du_commutativeSemiring_320 (coe v0))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.commutativeSemigroup
d_commutativeSemigroup_796 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_666
d_commutativeSemigroup_796 ~v0 ~v1 v2
  = du_commutativeSemigroup_796 v2
du_commutativeSemigroup_796 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_666
du_commutativeSemigroup_796 v0
  = let v1 = coe du_commutativeSemiring_320 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Bundles.du_commutativeSemigroup_1052
         (coe
            MAlonzo.Code.Algebra.Bundles.du_'42''45'commutativeMonoid_2642
            (coe v1)))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.*-cong
d_'42''45'cong_798 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_798 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'cong_1508
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
            (coe
               d_isCommutativeSemiring_62
               (coe d_isAlmostCommutativeRing_214 (coe v0)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.∙-congʳ
d_'8729''45'cong'691'_800 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_800 ~v0 ~v1 v2
  = du_'8729''45'cong'691'_800 v2
du_'8729''45'cong'691'_800 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_800 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = coe
                          MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1568
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v5) in
                   coe
                     (let v7 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v6) in
                      coe
                        (let v8
                               = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v7) in
                         coe
                           (let v9
                                  = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 (coe v7) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                                 (coe v9)
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                       (coe v8))))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.∙-congˡ
d_'8729''45'cong'737'_802 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_802 ~v0 ~v1 v2
  = du_'8729''45'cong'737'_802 v2
du_'8729''45'cong'737'_802 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_802 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = coe
                          MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1568
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v5) in
                   coe
                     (let v7 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v6) in
                      coe
                        (let v8
                               = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v7) in
                         coe
                           (let v9
                                  = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 (coe v7) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                                 (coe v9)
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                       (coe v8))))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.*-identity
d_'42''45'identity_804 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_804 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1512
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
            (coe
               d_isCommutativeSemiring_62
               (coe d_isAlmostCommutativeRing_214 (coe v0)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.identityʳ
d_identity'691'_806 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
d_identity'691'_806 ~v0 ~v1 v2 = du_identity'691'_806 v2
du_identity'691'_806 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
du_identity'691'_806 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_identity'691'_726
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1568
                     (coe v4))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.identityˡ
d_identity'737'_808 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
d_identity'737'_808 ~v0 ~v1 v2 = du_identity'737'_808 v2
du_identity'737'_808 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
du_identity'737'_808 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_identity'737'_724
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1568
                     (coe v4))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.isCommutativeMagma
d_isCommutativeMagma_810 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
d_isCommutativeMagma_810 ~v0 ~v1 v2 = du_isCommutativeMagma_810 v2
du_isCommutativeMagma_810 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
du_isCommutativeMagma_810 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1798
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_584
               (coe
                  MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1472
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.*-isCommutativeMonoid
d_'42''45'isCommutativeMonoid_812 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
d_'42''45'isCommutativeMonoid_812 ~v0 ~v1 v2
  = du_'42''45'isCommutativeMonoid_812 v2
du_'42''45'isCommutativeMonoid_812 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
du_'42''45'isCommutativeMonoid_812 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeMonoid_1806
         (coe d_isCommutativeSemiring_62 (coe v1)))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_814 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
d_'42''45'isCommutativeSemigroup_814 ~v0 ~v1 v2
  = du_'42''45'isCommutativeSemigroup_814 v2
du_'42''45'isCommutativeSemigroup_814 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
du_'42''45'isCommutativeSemigroup_814 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1472
            (coe
               MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1798
               (coe v2))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.*-isMagma
d_'42''45'isMagma_816 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'42''45'isMagma_816 ~v0 ~v1 v2 = du_'42''45'isMagma_816 v2
du_'42''45'isMagma_816 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_'42''45'isMagma_816 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1564
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.*-isMonoid
d_'42''45'isMonoid_818 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
d_'42''45'isMonoid_818 ~v0 ~v1 v2 = du_'42''45'isMonoid_818 v2
du_'42''45'isMonoid_818 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
du_'42''45'isMonoid_818 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1568
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.*-isSemigroup
d_'42''45'isSemigroup_820 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_'42''45'isSemigroup_820 ~v0 ~v1 v2
  = du_'42''45'isSemigroup_820 v2
du_'42''45'isSemigroup_820 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
du_'42''45'isSemigroup_820 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1566
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.magma
d_magma_822 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_72
d_magma_822 ~v0 ~v1 v2 = du_magma_822 v2
du_magma_822 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_72
du_magma_822 v0
  = let v1 = coe du_commutativeSemiring_320 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_semiring_2600 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
                    (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Bundles.du_'42''45'monoid_2288 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Bundles.du_magma_588
                  (coe MAlonzo.Code.Algebra.Bundles.du_semigroup_948 (coe v4))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.*-monoid
d_'42''45'monoid_824 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886
d_'42''45'monoid_824 ~v0 ~v1 v2 = du_'42''45'monoid_824 v2
du_'42''45'monoid_824 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886
du_'42''45'monoid_824 v0
  = let v1 = coe du_commutativeSemiring_320 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_semiring_2600 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Bundles.du_'42''45'monoid_2288
            (coe
               MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
               (coe v2))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.semigroup
d_semigroup_826 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_540
d_semigroup_826 ~v0 ~v1 v2 = du_semigroup_826 v2
du_semigroup_826 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_540
du_semigroup_826 v0
  = let v1 = coe du_commutativeSemiring_320 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_semiring_2600 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Bundles.du_semigroup_948
               (coe
                  MAlonzo.Code.Algebra.Bundles.du_'42''45'monoid_2288 (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.assoc
d_assoc_828 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_828 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_assoc_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_744
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                     (coe
                        d_isCommutativeSemiring_62
                        (coe d_isAlmostCommutativeRing_214 (coe v0))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.comm
d_comm_830 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_830 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_comm_746
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
               (coe
                  d_isCommutativeSemiring_62
                  (coe d_isAlmostCommutativeRing_214 (coe v0))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.+-commutativeMonoid
d_'43''45'commutativeMonoid_832 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_966
d_'43''45'commutativeMonoid_832 ~v0 ~v1 v2
  = du_'43''45'commutativeMonoid_832 v2
du_'43''45'commutativeMonoid_832 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_966
du_'43''45'commutativeMonoid_832 v0
  = let v1 = coe du_commutativeSemiring_320 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_semiring_2600 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Bundles.du_'43''45'commutativeMonoid_2266
            (coe
               MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
               (coe v2))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.∙-cong
d_'8729''45'cong_834 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_834 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_478
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_744
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                        (coe
                           d_isCommutativeSemiring_62
                           (coe d_isAlmostCommutativeRing_214 (coe v0)))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.∙-congʳ
d_'8729''45'cong'691'_836 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_836 ~v0 ~v1 v2
  = du_'8729''45'cong'691'_836 v2
du_'8729''45'cong'691'_836 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_836 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v6) in
                      coe
                        (let v8 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v7) in
                         coe
                           (let v9
                                  = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v8) in
                            coe
                              (let v10
                                     = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                         (coe v8) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                                    (coe v10)
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                          (coe v9)))))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.∙-congˡ
d_'8729''45'cong'737'_838 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_838 ~v0 ~v1 v2
  = du_'8729''45'cong'737'_838 v2
du_'8729''45'cong'737'_838 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_838 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v6) in
                      coe
                        (let v8 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v7) in
                         coe
                           (let v9
                                  = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v8) in
                            coe
                              (let v10
                                     = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                         (coe v8) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                                    (coe v10)
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                          (coe v9)))))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.identity
d_identity_840 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_840 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_696
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_744
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                  (coe
                     d_isCommutativeSemiring_62
                     (coe d_isAlmostCommutativeRing_214 (coe v0)))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.identityʳ
d_identity'691'_842 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
d_identity'691'_842 ~v0 ~v1 v2 = du_identity'691'_842 v2
du_identity'691'_842 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
du_identity'691'_842 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_identity'691'_726
                     (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v5)))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.identityˡ
d_identity'737'_844 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
d_identity'737'_844 ~v0 ~v1 v2 = du_identity'737'_844 v2
du_identity'737'_844 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
du_identity'737'_844 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_identity'737'_724
                     (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v5)))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.isCommutativeMagma
d_isCommutativeMagma_846 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
d_isCommutativeMagma_846 ~v0 ~v1 v2 = du_isCommutativeMagma_846 v2
du_isCommutativeMagma_846 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
du_isCommutativeMagma_846 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_584
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_784
                        (coe v5)))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_848 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
d_'43''45'isCommutativeMonoid_848 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
            (coe
               d_isCommutativeSemiring_62
               (coe d_isAlmostCommutativeRing_214 (coe v0)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.isCommutativeSemigroup
d_isCommutativeSemigroup_850 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
d_isCommutativeSemigroup_850 ~v0 ~v1 v2
  = du_isCommutativeSemigroup_850 v2
du_isCommutativeSemigroup_850 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
du_isCommutativeSemigroup_850 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_784
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                     (coe v4))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.isMagma
d_isMagma_852 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_852 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_478
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_744
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                     (coe
                        d_isCommutativeSemiring_62
                        (coe d_isAlmostCommutativeRing_214 (coe v0))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.isMonoid
d_isMonoid_854 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
d_isMonoid_854 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_744
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
               (coe
                  d_isCommutativeSemiring_62
                  (coe d_isAlmostCommutativeRing_214 (coe v0))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.isSemigroup
d_isSemigroup_856 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_isSemigroup_856 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_744
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                  (coe
                     d_isCommutativeSemiring_62
                     (coe d_isAlmostCommutativeRing_214 (coe v0)))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.isUnitalMagma
d_isUnitalMagma_858 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_640
d_isUnitalMagma_858 ~v0 ~v1 v2 = du_isUnitalMagma_858 v2
du_isUnitalMagma_858 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_640
du_isUnitalMagma_858 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_728
                     (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v5)))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.magma
d_magma_860 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_72
d_magma_860 ~v0 ~v1 v2 = du_magma_860 v2
du_magma_860 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_72
du_magma_860 v0
  = let v1 = coe du_commutativeSemiring_320 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_semiring_2600 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
                    (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Bundles.du_'43''45'commutativeMonoid_2266
                       (coe v3) in
             coe
               (let v5
                      = coe MAlonzo.Code.Algebra.Bundles.du_monoid_1036 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Bundles.du_magma_588
                     (coe MAlonzo.Code.Algebra.Bundles.du_semigroup_948 (coe v5)))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.monoid
d_monoid_862 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886
d_monoid_862 ~v0 ~v1 v2 = du_monoid_862 v2
du_monoid_862 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886
du_monoid_862 v0
  = let v1 = coe du_commutativeSemiring_320 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_semiring_2600 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Bundles.du_monoid_1036
               (coe
                  MAlonzo.Code.Algebra.Bundles.du_'43''45'commutativeMonoid_2266
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.semigroup
d_semigroup_864 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_540
d_semigroup_864 ~v0 ~v1 v2 = du_semigroup_864 v2
du_semigroup_864 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_540
du_semigroup_864 v0
  = let v1 = coe du_commutativeSemiring_320 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_semiring_2600 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
                    (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Bundles.du_'43''45'commutativeMonoid_2266
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Bundles.du_semigroup_948
                  (coe MAlonzo.Code.Algebra.Bundles.du_monoid_1036 (coe v4))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.-_
d_'45'__866 :: T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
d_'45'__866 v0 = coe d_'45'__208 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.-‿*-distribˡ
d_'45''8255''42''45'distrib'737'_868 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny -> AgdaAny
d_'45''8255''42''45'distrib'737'_868 v0
  = coe
      d_'45''8255''42''45'distrib'737'_70
      (coe d_isAlmostCommutativeRing_214 (coe v0))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.-‿+-comm
d_'45''8255''43''45'comm_870 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny -> AgdaAny
d_'45''8255''43''45'comm_870 v0
  = coe
      d_'45''8255''43''45'comm_76
      (coe d_isAlmostCommutativeRing_214 (coe v0))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.-‿cong
d_'45''8255'cong_872 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'45''8255'cong_872 v0
  = coe
      d_'45''8255'cong_64 (coe d_isAlmostCommutativeRing_214 (coe v0))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.0#
d_0'35'_874 :: T_AlmostCommutativeRing_178 -> AgdaAny
d_0'35'_874 v0 = coe d_0'35'_210 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.1#
d_1'35'_876 :: T_AlmostCommutativeRing_178 -> AgdaAny
d_1'35'_876 v0 = coe d_1'35'_212 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.Carrier
d_Carrier_878 :: T_AlmostCommutativeRing_178 -> ()
d_Carrier_878 = erased
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.commutativeSemiring
d_commutativeSemiring_880 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemiring_2470
d_commutativeSemiring_880 ~v0 ~v1 v2
  = du_commutativeSemiring_880 v2
du_commutativeSemiring_880 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemiring_2470
du_commutativeSemiring_880 v0
  = coe du_commutativeSemiring_320 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.distrib
d_distrib_882 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_882 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1514
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
            (coe
               d_isCommutativeSemiring_62
               (coe d_isAlmostCommutativeRing_214 (coe v0)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.distribʳ
d_distrib'691'_884 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_884 ~v0 ~v1 v2 = du_distrib'691'_884 v2
du_distrib'691'_884 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'691'_884 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_distrib'691'_1518
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.distribˡ
d_distrib'737'_886 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_886 ~v0 ~v1 v2 = du_distrib'737'_886 v2
du_distrib'737'_886 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'737'_886 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_distrib'737'_1516
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.isAlmostCommutativeRing
d_isAlmostCommutativeRing_888 ::
  T_AlmostCommutativeRing_178 -> T_IsAlmostCommutativeRing_26
d_isAlmostCommutativeRing_888 v0
  = coe d_isAlmostCommutativeRing_214 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.isCommutativeSemiring
d_isCommutativeSemiring_890 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1696
d_isCommutativeSemiring_890 v0
  = coe
      d_isCommutativeSemiring_62
      (coe d_isAlmostCommutativeRing_214 (coe v0))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.isCommutativeSemiringWithoutOne
d_isCommutativeSemiringWithoutOne_892 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1390
d_isCommutativeSemiringWithoutOne_892 ~v0 ~v1 v2
  = du_isCommutativeSemiringWithoutOne_892 v2
du_isCommutativeSemiringWithoutOne_892 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1390
du_isCommutativeSemiringWithoutOne_892 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1798
         (coe d_isCommutativeSemiring_62 (coe v1)))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.isEquivalence
d_isEquivalence_894 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_894 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_478
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_744
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                        (coe
                           d_isCommutativeSemiring_62
                           (coe d_isAlmostCommutativeRing_214 (coe v0)))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.isNearSemiring
d_isNearSemiring_896 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1216
d_isNearSemiring_896 ~v0 ~v1 v2 = du_isNearSemiring_896 v2
du_isNearSemiring_896 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1216
du_isNearSemiring_896 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_isNearSemiring_1382
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1678
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.isPartialEquivalence
d_isPartialEquivalence_898 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_898 ~v0 ~v1 v2
  = du_isPartialEquivalence_898 v2
du_isPartialEquivalence_898 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_898 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v6) in
                      coe
                        (let v8 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v7) in
                         coe
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                 (coe v8))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.isSemiring
d_isSemiring_900 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1588
d_isSemiring_900 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
      (coe
         d_isCommutativeSemiring_62
         (coe d_isAlmostCommutativeRing_214 (coe v0)))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_902 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1486
d_isSemiringWithoutAnnihilatingZero_902 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
         (coe
            d_isCommutativeSemiring_62
            (coe d_isAlmostCommutativeRing_214 (coe v0))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.isSemiringWithoutOne
d_isSemiringWithoutOne_904 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1296
d_isSemiringWithoutOne_904 ~v0 ~v1 v2
  = du_isSemiringWithoutOne_904 v2
du_isSemiringWithoutOne_904 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1296
du_isSemiringWithoutOne_904 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1678
            (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.rawRing
d_rawRing_906 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276
d_rawRing_906 ~v0 ~v1 v2 = du_rawRing_906 v2
du_rawRing_906 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276
du_rawRing_906 v0 = coe du_rawRing_344 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.refl
d_refl_908 :: T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
d_refl_908 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_478
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                           (coe
                              d_isCommutativeSemiring_62
                              (coe d_isAlmostCommutativeRing_214 (coe v0))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.reflexive
d_reflexive_910 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_910 ~v0 ~v1 v2 = du_reflexive_910 v2
du_reflexive_910 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_910 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v6) in
                      coe
                        (let v8 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v7) in
                         coe
                           (\ v9 v10 v11 ->
                              coe
                                MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                                (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v8))
                                v9))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.semiring
d_semiring_912 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Semiring_2304
d_semiring_912 ~v0 ~v1 v2 = du_semiring_912 v2
du_semiring_912 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Semiring_2304
du_semiring_912 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.du_semiring_2600
      (coe du_commutativeSemiring_320 (coe v0))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.setoid
d_setoid_914 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_914 ~v0 ~v1 v2 = du_setoid_914 v2
du_setoid_914 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_914 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v6) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_setoid_200
                           (coe MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v7)))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.sym
d_sym_916 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_916 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_478
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                           (coe
                              d_isCommutativeSemiring_62
                              (coe d_isAlmostCommutativeRing_214 (coe v0))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.trans
d_trans_918 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_918 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_478
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                           (coe
                              d_isCommutativeSemiring_62
                              (coe d_isAlmostCommutativeRing_214 (coe v0))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.zero
d_zero_920 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_920 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_1604
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
         (coe
            d_isCommutativeSemiring_62
            (coe d_isAlmostCommutativeRing_214 (coe v0))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.zeroʳ
d_zero'691'_922 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
d_zero'691'_922 ~v0 ~v1 v2 = du_zero'691'_922 v2
du_zero'691'_922 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
du_zero'691'_922 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_zero'691'_1380
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1678
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.zeroˡ
d_zero'737'_924 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
d_zero'737'_924 ~v0 ~v1 v2 = du_zero'737'_924 v2
du_zero'737'_924 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
du_zero'737'_924 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_zero'737'_1378
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1678
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.Induced-equivalence
d_Induced'45'equivalence_948 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> ()
d_Induced'45'equivalence_948 = erased
-- Algebra.Solver.Ring.AlmostCommutativeRing._._._*_
d__'42'__964 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d__'42'__964 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 = du__'42'__964 v5
du__'42'__964 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny -> AgdaAny
du__'42'__964 v0 = coe d__'42'__206 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing._._._+_
d__'43'__966 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d__'43'__966 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 = du__'43'__966 v5
du__'43'__966 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny -> AgdaAny
du__'43'__966 v0 = coe d__'43'__204 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing._._._≈_
d__'8776'__968 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()
d__'8776'__968 = erased
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.*-assoc
d_'42''45'assoc_970 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_970 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_'42''45'assoc_970 v5
du_'42''45'assoc_970 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'42''45'assoc_970 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'assoc_1510
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
            (coe
               d_isCommutativeSemiring_62
               (coe d_isAlmostCommutativeRing_214 (coe v0)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.*-comm
d_'42''45'comm_972 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'comm_972 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_'42''45'comm_972 v5
du_'42''45'comm_972 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny -> AgdaAny
du_'42''45'comm_972 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'comm_1712
      (coe
         d_isCommutativeSemiring_62
         (coe d_isAlmostCommutativeRing_214 (coe v0)))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.*-commutativeMonoid
d_'42''45'commutativeMonoid_974 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_966
d_'42''45'commutativeMonoid_974 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_'42''45'commutativeMonoid_974 v5
du_'42''45'commutativeMonoid_974 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_966
du_'42''45'commutativeMonoid_974 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.du_'42''45'commutativeMonoid_2642
      (coe du_commutativeSemiring_320 (coe v0))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.commutativeSemigroup
d_commutativeSemigroup_976 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_666
d_commutativeSemigroup_976 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_commutativeSemigroup_976 v5
du_commutativeSemigroup_976 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_666
du_commutativeSemigroup_976 v0
  = let v1 = coe du_commutativeSemiring_320 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Bundles.du_commutativeSemigroup_1052
         (coe
            MAlonzo.Code.Algebra.Bundles.du_'42''45'commutativeMonoid_2642
            (coe v1)))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.*-cong
d_'42''45'cong_978 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_978 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_'42''45'cong_978 v5
du_'42''45'cong_978 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'42''45'cong_978 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'cong_1508
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
            (coe
               d_isCommutativeSemiring_62
               (coe d_isAlmostCommutativeRing_214 (coe v0)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.∙-congʳ
d_'8729''45'cong'691'_980 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_980 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_'8729''45'cong'691'_980 v5
du_'8729''45'cong'691'_980 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_980 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = coe
                          MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1568
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v5) in
                   coe
                     (let v7 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v6) in
                      coe
                        (let v8
                               = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v7) in
                         coe
                           (let v9
                                  = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 (coe v7) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                                 (coe v9)
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                       (coe v8))))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.∙-congˡ
d_'8729''45'cong'737'_982 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_982 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_'8729''45'cong'737'_982 v5
du_'8729''45'cong'737'_982 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_982 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = coe
                          MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1568
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v5) in
                   coe
                     (let v7 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v6) in
                      coe
                        (let v8
                               = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v7) in
                         coe
                           (let v9
                                  = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 (coe v7) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                                 (coe v9)
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                       (coe v8))))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.*-identity
d_'42''45'identity_984 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_984 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_'42''45'identity_984 v5
du_'42''45'identity_984 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'42''45'identity_984 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1512
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
            (coe
               d_isCommutativeSemiring_62
               (coe d_isAlmostCommutativeRing_214 (coe v0)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.identityʳ
d_identity'691'_986 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_identity'691'_986 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_identity'691'_986 v5
du_identity'691'_986 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
du_identity'691'_986 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_identity'691'_726
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1568
                     (coe v4))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.identityˡ
d_identity'737'_988 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_identity'737'_988 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_identity'737'_988 v5
du_identity'737'_988 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
du_identity'737'_988 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_identity'737'_724
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1568
                     (coe v4))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.isCommutativeMagma
d_isCommutativeMagma_990 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
d_isCommutativeMagma_990 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_isCommutativeMagma_990 v5
du_isCommutativeMagma_990 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
du_isCommutativeMagma_990 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1798
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_584
               (coe
                  MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1472
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.*-isCommutativeMonoid
d_'42''45'isCommutativeMonoid_992 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
d_'42''45'isCommutativeMonoid_992 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7
                                  ~v8
  = du_'42''45'isCommutativeMonoid_992 v5
du_'42''45'isCommutativeMonoid_992 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
du_'42''45'isCommutativeMonoid_992 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeMonoid_1806
         (coe d_isCommutativeSemiring_62 (coe v1)))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_994 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
d_'42''45'isCommutativeSemigroup_994 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7
                                     ~v8
  = du_'42''45'isCommutativeSemigroup_994 v5
du_'42''45'isCommutativeSemigroup_994 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
du_'42''45'isCommutativeSemigroup_994 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1472
            (coe
               MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1798
               (coe v2))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.*-isMagma
d_'42''45'isMagma_996 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'42''45'isMagma_996 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_'42''45'isMagma_996 v5
du_'42''45'isMagma_996 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_'42''45'isMagma_996 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1564
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.*-isMonoid
d_'42''45'isMonoid_998 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
d_'42''45'isMonoid_998 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_'42''45'isMonoid_998 v5
du_'42''45'isMonoid_998 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
du_'42''45'isMonoid_998 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1568
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.*-isSemigroup
d_'42''45'isSemigroup_1000 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_'42''45'isSemigroup_1000 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_'42''45'isSemigroup_1000 v5
du_'42''45'isSemigroup_1000 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
du_'42''45'isSemigroup_1000 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1566
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.magma
d_magma_1002 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Algebra.Bundles.T_Magma_72
d_magma_1002 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 = du_magma_1002 v5
du_magma_1002 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_72
du_magma_1002 v0
  = let v1 = coe du_commutativeSemiring_320 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_semiring_2600 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
                    (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Bundles.du_'42''45'monoid_2288 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Bundles.du_magma_588
                  (coe MAlonzo.Code.Algebra.Bundles.du_semigroup_948 (coe v4))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.*-monoid
d_'42''45'monoid_1004 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Algebra.Bundles.T_Monoid_886
d_'42''45'monoid_1004 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_'42''45'monoid_1004 v5
du_'42''45'monoid_1004 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886
du_'42''45'monoid_1004 v0
  = let v1 = coe du_commutativeSemiring_320 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_semiring_2600 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Bundles.du_'42''45'monoid_2288
            (coe
               MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
               (coe v2))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.semigroup
d_semigroup_1006 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Algebra.Bundles.T_Semigroup_540
d_semigroup_1006 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_semigroup_1006 v5
du_semigroup_1006 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_540
du_semigroup_1006 v0
  = let v1 = coe du_commutativeSemiring_320 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_semiring_2600 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Bundles.du_semigroup_948
               (coe
                  MAlonzo.Code.Algebra.Bundles.du_'42''45'monoid_2288 (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.assoc
d_assoc_1008 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_1008 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 = du_assoc_1008 v5
du_assoc_1008 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_assoc_1008 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_assoc_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_744
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                     (coe
                        d_isCommutativeSemiring_62
                        (coe d_isAlmostCommutativeRing_214 (coe v0))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.comm
d_comm_1010 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_1010 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 = du_comm_1010 v5
du_comm_1010 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny -> AgdaAny
du_comm_1010 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_comm_746
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
               (coe
                  d_isCommutativeSemiring_62
                  (coe d_isAlmostCommutativeRing_214 (coe v0))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.+-commutativeMonoid
d_'43''45'commutativeMonoid_1012 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_966
d_'43''45'commutativeMonoid_1012 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_'43''45'commutativeMonoid_1012 v5
du_'43''45'commutativeMonoid_1012 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_966
du_'43''45'commutativeMonoid_1012 v0
  = let v1 = coe du_commutativeSemiring_320 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_semiring_2600 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Bundles.du_'43''45'commutativeMonoid_2266
            (coe
               MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
               (coe v2))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.∙-cong
d_'8729''45'cong_1014 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_1014 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_'8729''45'cong_1014 v5
du_'8729''45'cong_1014 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong_1014 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_478
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_744
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                        (coe
                           d_isCommutativeSemiring_62
                           (coe d_isAlmostCommutativeRing_214 (coe v0)))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.∙-congʳ
d_'8729''45'cong'691'_1016 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_1016 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_'8729''45'cong'691'_1016 v5
du_'8729''45'cong'691'_1016 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_1016 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v6) in
                      coe
                        (let v8 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v7) in
                         coe
                           (let v9
                                  = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v8) in
                            coe
                              (let v10
                                     = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                         (coe v8) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                                    (coe v10)
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                          (coe v9)))))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.∙-congˡ
d_'8729''45'cong'737'_1018 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_1018 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_'8729''45'cong'737'_1018 v5
du_'8729''45'cong'737'_1018 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_1018 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v6) in
                      coe
                        (let v8 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v7) in
                         coe
                           (let v9
                                  = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v8) in
                            coe
                              (let v10
                                     = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                         (coe v8) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                                    (coe v10)
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                          (coe v9)))))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.identity
d_identity_1020 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1020 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_identity_1020 v5
du_identity_1020 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_identity_1020 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_696
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_744
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                  (coe
                     d_isCommutativeSemiring_62
                     (coe d_isAlmostCommutativeRing_214 (coe v0)))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.identityʳ
d_identity'691'_1022 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_identity'691'_1022 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_identity'691'_1022 v5
du_identity'691'_1022 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
du_identity'691'_1022 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_identity'691'_726
                     (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v5)))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.identityˡ
d_identity'737'_1024 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_identity'737'_1024 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_identity'737'_1024 v5
du_identity'737'_1024 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
du_identity'737'_1024 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_identity'737'_724
                     (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v5)))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.isCommutativeMagma
d_isCommutativeMagma_1026 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
d_isCommutativeMagma_1026 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_isCommutativeMagma_1026 v5
du_isCommutativeMagma_1026 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
du_isCommutativeMagma_1026 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_584
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_784
                        (coe v5)))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_1028 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
d_'43''45'isCommutativeMonoid_1028 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7
                                   ~v8
  = du_'43''45'isCommutativeMonoid_1028 v5
du_'43''45'isCommutativeMonoid_1028 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
du_'43''45'isCommutativeMonoid_1028 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
            (coe
               d_isCommutativeSemiring_62
               (coe d_isAlmostCommutativeRing_214 (coe v0)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.isCommutativeSemigroup
d_isCommutativeSemigroup_1030 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
d_isCommutativeSemigroup_1030 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_isCommutativeSemigroup_1030 v5
du_isCommutativeSemigroup_1030 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
du_isCommutativeSemigroup_1030 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_784
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                     (coe v4))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.isMagma
d_isMagma_1032 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_1032 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_isMagma_1032 v5
du_isMagma_1032 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_isMagma_1032 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_478
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_744
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                     (coe
                        d_isCommutativeSemiring_62
                        (coe d_isAlmostCommutativeRing_214 (coe v0))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.isMonoid
d_isMonoid_1034 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
d_isMonoid_1034 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_isMonoid_1034 v5
du_isMonoid_1034 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
du_isMonoid_1034 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_744
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
               (coe
                  d_isCommutativeSemiring_62
                  (coe d_isAlmostCommutativeRing_214 (coe v0))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.isSemigroup
d_isSemigroup_1036 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_isSemigroup_1036 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_isSemigroup_1036 v5
du_isSemigroup_1036 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
du_isSemigroup_1036 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_744
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                  (coe
                     d_isCommutativeSemiring_62
                     (coe d_isAlmostCommutativeRing_214 (coe v0)))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.isUnitalMagma
d_isUnitalMagma_1038 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_640
d_isUnitalMagma_1038 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_isUnitalMagma_1038 v5
du_isUnitalMagma_1038 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_640
du_isUnitalMagma_1038 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_728
                     (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v5)))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.magma
d_magma_1040 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Algebra.Bundles.T_Magma_72
d_magma_1040 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 = du_magma_1040 v5
du_magma_1040 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_72
du_magma_1040 v0
  = let v1 = coe du_commutativeSemiring_320 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_semiring_2600 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
                    (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Bundles.du_'43''45'commutativeMonoid_2266
                       (coe v3) in
             coe
               (let v5
                      = coe MAlonzo.Code.Algebra.Bundles.du_monoid_1036 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Bundles.du_magma_588
                     (coe MAlonzo.Code.Algebra.Bundles.du_semigroup_948 (coe v5)))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.monoid
d_monoid_1042 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Algebra.Bundles.T_Monoid_886
d_monoid_1042 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_monoid_1042 v5
du_monoid_1042 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886
du_monoid_1042 v0
  = let v1 = coe du_commutativeSemiring_320 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_semiring_2600 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Bundles.du_monoid_1036
               (coe
                  MAlonzo.Code.Algebra.Bundles.du_'43''45'commutativeMonoid_2266
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.semigroup
d_semigroup_1044 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Algebra.Bundles.T_Semigroup_540
d_semigroup_1044 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_semigroup_1044 v5
du_semigroup_1044 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_540
du_semigroup_1044 v0
  = let v1 = coe du_commutativeSemiring_320 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_semiring_2600 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
                    (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Bundles.du_'43''45'commutativeMonoid_2266
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Bundles.du_semigroup_948
                  (coe MAlonzo.Code.Algebra.Bundles.du_monoid_1036 (coe v4))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.-_
d_'45'__1046 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'45'__1046 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 = du_'45'__1046 v5
du_'45'__1046 :: T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
du_'45'__1046 v0 = coe d_'45'__208 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.-‿*-distribˡ
d_'45''8255''42''45'distrib'737'_1048 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'45''8255''42''45'distrib'737'_1048 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
                                      ~v7 ~v8
  = du_'45''8255''42''45'distrib'737'_1048 v5
du_'45''8255''42''45'distrib'737'_1048 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny -> AgdaAny
du_'45''8255''42''45'distrib'737'_1048 v0
  = coe
      d_'45''8255''42''45'distrib'737'_70
      (coe d_isAlmostCommutativeRing_214 (coe v0))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.-‿+-comm
d_'45''8255''43''45'comm_1050 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'45''8255''43''45'comm_1050 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_'45''8255''43''45'comm_1050 v5
du_'45''8255''43''45'comm_1050 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny -> AgdaAny
du_'45''8255''43''45'comm_1050 v0
  = coe
      d_'45''8255''43''45'comm_76
      (coe d_isAlmostCommutativeRing_214 (coe v0))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.-‿cong
d_'45''8255'cong_1052 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'45''8255'cong_1052 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_'45''8255'cong_1052 v5
du_'45''8255'cong_1052 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'45''8255'cong_1052 v0
  = coe
      d_'45''8255'cong_64 (coe d_isAlmostCommutativeRing_214 (coe v0))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.0#
d_0'35'_1054 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_0'35'_1054 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 = du_0'35'_1054 v5
du_0'35'_1054 :: T_AlmostCommutativeRing_178 -> AgdaAny
du_0'35'_1054 v0 = coe d_0'35'_210 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.1#
d_1'35'_1056 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_1'35'_1056 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 = du_1'35'_1056 v5
du_1'35'_1056 :: T_AlmostCommutativeRing_178 -> AgdaAny
du_1'35'_1056 v0 = coe d_1'35'_212 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.Carrier
d_Carrier_1058 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> ()
d_Carrier_1058 = erased
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.commutativeSemiring
d_commutativeSemiring_1060 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Algebra.Bundles.T_CommutativeSemiring_2470
d_commutativeSemiring_1060 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_commutativeSemiring_1060 v5
du_commutativeSemiring_1060 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemiring_2470
du_commutativeSemiring_1060 v0
  = coe du_commutativeSemiring_320 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.distrib
d_distrib_1062 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1062 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_distrib_1062 v5
du_distrib_1062 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_distrib_1062 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1514
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
            (coe
               d_isCommutativeSemiring_62
               (coe d_isAlmostCommutativeRing_214 (coe v0)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.distribʳ
d_distrib'691'_1064 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_1064 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_distrib'691'_1064 v5
du_distrib'691'_1064 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'691'_1064 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_distrib'691'_1518
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.distribˡ
d_distrib'737'_1066 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_1066 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_distrib'737'_1066 v5
du_distrib'737'_1066 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'737'_1066 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_distrib'737'_1516
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.isAlmostCommutativeRing
d_isAlmostCommutativeRing_1068 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> T_IsAlmostCommutativeRing_26
d_isAlmostCommutativeRing_1068 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_isAlmostCommutativeRing_1068 v5
du_isAlmostCommutativeRing_1068 ::
  T_AlmostCommutativeRing_178 -> T_IsAlmostCommutativeRing_26
du_isAlmostCommutativeRing_1068 v0
  = coe d_isAlmostCommutativeRing_214 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.isCommutativeSemiring
d_isCommutativeSemiring_1070 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1696
d_isCommutativeSemiring_1070 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_isCommutativeSemiring_1070 v5
du_isCommutativeSemiring_1070 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1696
du_isCommutativeSemiring_1070 v0
  = coe
      d_isCommutativeSemiring_62
      (coe d_isAlmostCommutativeRing_214 (coe v0))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.isCommutativeSemiringWithoutOne
d_isCommutativeSemiringWithoutOne_1072 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1390
d_isCommutativeSemiringWithoutOne_1072 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
                                       ~v7 ~v8
  = du_isCommutativeSemiringWithoutOne_1072 v5
du_isCommutativeSemiringWithoutOne_1072 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1390
du_isCommutativeSemiringWithoutOne_1072 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1798
         (coe d_isCommutativeSemiring_62 (coe v1)))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.isEquivalence
d_isEquivalence_1074 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1074 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_isEquivalence_1074 v5
du_isEquivalence_1074 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_1074 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_478
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_744
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                        (coe
                           d_isCommutativeSemiring_62
                           (coe d_isAlmostCommutativeRing_214 (coe v0)))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.isNearSemiring
d_isNearSemiring_1076 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1216
d_isNearSemiring_1076 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_isNearSemiring_1076 v5
du_isNearSemiring_1076 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1216
du_isNearSemiring_1076 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_isNearSemiring_1382
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1678
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.isPartialEquivalence
d_isPartialEquivalence_1078 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1078 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_isPartialEquivalence_1078 v5
du_isPartialEquivalence_1078 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1078 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v6) in
                      coe
                        (let v8 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v7) in
                         coe
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                 (coe v8))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.isSemiring
d_isSemiring_1080 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Algebra.Structures.T_IsSemiring_1588
d_isSemiring_1080 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_isSemiring_1080 v5
du_isSemiring_1080 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1588
du_isSemiring_1080 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
      (coe
         d_isCommutativeSemiring_62
         (coe d_isAlmostCommutativeRing_214 (coe v0)))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_1082 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1486
d_isSemiringWithoutAnnihilatingZero_1082 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
                                         ~v7 ~v8
  = du_isSemiringWithoutAnnihilatingZero_1082 v5
du_isSemiringWithoutAnnihilatingZero_1082 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1486
du_isSemiringWithoutAnnihilatingZero_1082 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
         (coe
            d_isCommutativeSemiring_62
            (coe d_isAlmostCommutativeRing_214 (coe v0))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.isSemiringWithoutOne
d_isSemiringWithoutOne_1084 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1296
d_isSemiringWithoutOne_1084 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_isSemiringWithoutOne_1084 v5
du_isSemiringWithoutOne_1084 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1296
du_isSemiringWithoutOne_1084 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1678
            (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.rawRing
d_rawRing_1086 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276
d_rawRing_1086 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_rawRing_1086 v5
du_rawRing_1086 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276
du_rawRing_1086 v0 = coe du_rawRing_344 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.refl
d_refl_1088 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_refl_1088 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 = du_refl_1088 v5
du_refl_1088 :: T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
du_refl_1088 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_478
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                           (coe
                              d_isCommutativeSemiring_62
                              (coe d_isAlmostCommutativeRing_214 (coe v0))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.reflexive
d_reflexive_1090 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1090 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_reflexive_1090 v5
du_reflexive_1090 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1090 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v6) in
                      coe
                        (let v8 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v7) in
                         coe
                           (\ v9 v10 v11 ->
                              coe
                                MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                                (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v8))
                                v9))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.semiring
d_semiring_1092 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Algebra.Bundles.T_Semiring_2304
d_semiring_1092 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_semiring_1092 v5
du_semiring_1092 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Bundles.T_Semiring_2304
du_semiring_1092 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.du_semiring_2600
      (coe du_commutativeSemiring_320 (coe v0))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.setoid
d_setoid_1094 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_1094 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_setoid_1094 v5
du_setoid_1094 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_1094 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v6) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_setoid_200
                           (coe MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v7)))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.sym
d_sym_1096 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1096 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 = du_sym_1096 v5
du_sym_1096 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_1096 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_478
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                           (coe
                              d_isCommutativeSemiring_62
                              (coe d_isAlmostCommutativeRing_214 (coe v0))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.trans
d_trans_1098 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1098 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 = du_trans_1098 v5
du_trans_1098 ::
  T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1098 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_478
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                           (coe
                              d_isCommutativeSemiring_62
                              (coe d_isAlmostCommutativeRing_214 (coe v0))))))))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.zero
d_zero_1100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_1100 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 = du_zero_1100 v5
du_zero_1100 ::
  T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_zero_1100 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_1604
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
         (coe
            d_isCommutativeSemiring_62
            (coe d_isAlmostCommutativeRing_214 (coe v0))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.zeroʳ
d_zero'691'_1102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_zero'691'_1102 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_zero'691'_1102 v5
du_zero'691'_1102 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
du_zero'691'_1102 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_zero'691'_1380
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1678
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.zeroˡ
d_zero'737'_1104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_zero'737'_1104 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_zero'737'_1104 v5
du_zero'737'_1104 ::
  T_AlmostCommutativeRing_178 -> AgdaAny -> AgdaAny
du_zero'737'_1104 v0
  = let v1 = d_isAlmostCommutativeRing_214 (coe v0) in
    coe
      (let v2 = d_isCommutativeSemiring_62 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_zero'737'_1378
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1678
                  (coe v3)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.*-homo
d_'42''45'homo_1108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_1108 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8
  = du_'42''45'homo_1108 v6
du_'42''45'homo_1108 ::
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'42''45'homo_1108 v0 = coe d_'42''45'homo_760 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.+-homo
d_'43''45'homo_1110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'43''45'homo_1110 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8
  = du_'43''45'homo_1110 v6
du_'43''45'homo_1110 ::
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'43''45'homo_1110 v0 = coe d_'43''45'homo_758 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.-‿homo
d_'45''8255'homo_1112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'45''8255'homo_1112 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8
  = du_'45''8255'homo_1112 v6
du_'45''8255'homo_1112 ::
  T__'45'Raw'45'AlmostCommutative'10230'__358 -> AgdaAny -> AgdaAny
du_'45''8255'homo_1112 v0 = coe d_'45''8255'homo_762 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.0-homo
d_0'45'homo_1114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_0'45'homo_1114 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8
  = du_0'45'homo_1114 v6
du_0'45'homo_1114 ::
  T__'45'Raw'45'AlmostCommutative'10230'__358 -> AgdaAny
du_0'45'homo_1114 v0 = coe d_0'45'homo_764 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.1-homo
d_1'45'homo_1116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_1'45'homo_1116 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8
  = du_1'45'homo_1116 v6
du_1'45'homo_1116 ::
  T__'45'Raw'45'AlmostCommutative'10230'__358 -> AgdaAny
du_1'45'homo_1116 v0 = coe d_1'45'homo_766 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing._._.⟦_⟧
d_'10214'_'10215'_1118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  T_AlmostCommutativeRing_178 ->
  T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'10214'_'10215'_1118 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8
  = du_'10214'_'10215'_1118 v6
du_'10214'_'10215'_1118 ::
  T__'45'Raw'45'AlmostCommutative'10230'__358 -> AgdaAny -> AgdaAny
du_'10214'_'10215'_1118 v0 = coe d_'10214'_'10215'_756 (coe v0)
-- Algebra.Solver.Ring.AlmostCommutativeRing.fromCommutativeRing
d_fromCommutativeRing_1124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeRing_4054 ->
  T_AlmostCommutativeRing_178
d_fromCommutativeRing_1124 ~v0 ~v1 v2
  = du_fromCommutativeRing_1124 v2
du_fromCommutativeRing_1124 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeRing_4054 ->
  T_AlmostCommutativeRing_178
du_fromCommutativeRing_1124 v0
  = coe
      C_AlmostCommutativeRing'46'constructor_5973
      (MAlonzo.Code.Algebra.Bundles.d__'43'__4080 (coe v0))
      (MAlonzo.Code.Algebra.Bundles.d__'42'__4082 (coe v0))
      (MAlonzo.Code.Algebra.Bundles.d_'45'__4084 (coe v0))
      (MAlonzo.Code.Algebra.Bundles.d_0'35'_4086 (coe v0))
      (MAlonzo.Code.Algebra.Bundles.d_1'35'_4088 (coe v0))
      (coe
         C_IsAlmostCommutativeRing'46'constructor_1027
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_2946
            (coe MAlonzo.Code.Algebra.Bundles.d__'43'__4080 (coe v0))
            (coe MAlonzo.Code.Algebra.Bundles.d__'42'__4082 (coe v0))
            (coe MAlonzo.Code.Algebra.Bundles.d_'45'__4084 (coe v0))
            (coe MAlonzo.Code.Algebra.Bundles.d_0'35'_4086 (coe v0))
            (coe
               MAlonzo.Code.Algebra.Bundles.d_isCommutativeRing_4090 (coe v0)))
         (let v1
                = MAlonzo.Code.Algebra.Bundles.d_isCommutativeRing_4090 (coe v0) in
          coe
            (let v2 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v1) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'8315''185''45'cong_1052
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                        (coe v2))))))
         (coe
            (\ v1 v2 ->
               let v3
                     = MAlonzo.Code.Algebra.Bundles.d_isCommutativeRing_4090 (coe v0) in
               coe
                 (let v4 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v3) in
                  coe
                    (coe
                       MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                       (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
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
                                         (coe v4)))))))
                       (coe
                          MAlonzo.Code.Algebra.Bundles.d_'45'__4084 v0
                          (coe MAlonzo.Code.Algebra.Bundles.d__'42'__4082 v0 v1 v2))
                       (coe
                          MAlonzo.Code.Algebra.Bundles.d__'42'__4082 v0
                          (coe MAlonzo.Code.Algebra.Bundles.d_'45'__4084 v0 v1) v2)
                       (coe
                          MAlonzo.Code.Algebra.Properties.RingWithoutOne.du_'45''8255'distrib'737''45''42'_260
                          (coe
                             MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988
                             (coe MAlonzo.Code.Algebra.Bundles.du_ring_4216 (coe v0)))
                          (coe v1) (coe v2))))))
         (coe
            MAlonzo.Code.Algebra.Properties.AbelianGroup.du_'8315''185''45''8729''45'comm_244
            (coe
               MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3986
               (coe MAlonzo.Code.Algebra.Bundles.du_ring_4216 (coe v0)))))
-- Algebra.Solver.Ring.AlmostCommutativeRing.fromCommutativeSemiring
d_fromCommutativeSemiring_1500 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemiring_2470 ->
  T_AlmostCommutativeRing_178
d_fromCommutativeSemiring_1500 ~v0 ~v1 v2
  = du_fromCommutativeSemiring_1500 v2
du_fromCommutativeSemiring_1500 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemiring_2470 ->
  T_AlmostCommutativeRing_178
du_fromCommutativeSemiring_1500 v0
  = coe
      C_AlmostCommutativeRing'46'constructor_5973
      (MAlonzo.Code.Algebra.Bundles.d__'43'__2494 (coe v0))
      (MAlonzo.Code.Algebra.Bundles.d__'42'__2496 (coe v0)) (\ v1 -> v1)
      (MAlonzo.Code.Algebra.Bundles.d_0'35'_2498 (coe v0))
      (MAlonzo.Code.Algebra.Bundles.d_1'35'_2500 (coe v0))
      (coe
         C_IsAlmostCommutativeRing'46'constructor_1027
         (coe
            MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemiring_2502 (coe v0))
         (coe (\ v1 v2 v3 -> v3))
         (coe
            (\ v1 v2 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                 (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                    (coe
                       MAlonzo.Code.Algebra.Structures.d_isMagma_478
                       (coe
                          MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                          (coe
                             MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                             (coe
                                MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                (coe
                                   MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                   (coe
                                      MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                      (coe
                                         MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemiring_2502
                                         (coe v0)))))))))
                 (coe MAlonzo.Code.Algebra.Bundles.d__'42'__2496 v0 v1 v2)))
         (coe
            (\ v1 v2 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                 (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                    (coe
                       MAlonzo.Code.Algebra.Structures.d_isMagma_478
                       (coe
                          MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                          (coe
                             MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                             (coe
                                MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                (coe
                                   MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                   (coe
                                      MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                      (coe
                                         MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemiring_2502
                                         (coe v0)))))))))
                 (coe MAlonzo.Code.Algebra.Bundles.d__'43'__2494 v0 v1 v2))))
