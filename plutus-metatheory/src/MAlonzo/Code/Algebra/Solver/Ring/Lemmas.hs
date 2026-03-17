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

module MAlonzo.Code.Algebra.Solver.Ring.Lemmas where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Bundles.Raw
import qualified MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Single
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Algebra.Solver.Ring.Lemmas._._*_
d__'42'__56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'42'__56 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du__'42'__56 v5
du__'42'__56 ::
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'42'__56 v0
  = coe
      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
      (coe v0)
-- Algebra.Solver.Ring.Lemmas._._+_
d__'43'__58 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'43'__58 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du__'43'__58 v5
du__'43'__58 ::
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'43'__58 v0
  = coe
      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
      (coe v0)
-- Algebra.Solver.Ring.Lemmas._._≈_
d__'8776'__60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__60 = erased
-- Algebra.Solver.Ring.Lemmas._.-_
d_'45'__138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny
d_'45'__138 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_'45'__138 v5
du_'45'__138 ::
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny
du_'45'__138 v0
  = coe
      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'45'__208
      (coe v0)
-- Algebra.Solver.Ring.Lemmas._.0#
d_0'35'_146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny
d_0'35'_146 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_0'35'_146 v5
du_0'35'_146 ::
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  AgdaAny
du_0'35'_146 v0
  = coe
      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
      (coe v0)
-- Algebra.Solver.Ring.Lemmas._.1#
d_1'35'_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny
d_1'35'_148 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_1'35'_148 v5
du_1'35'_148 ::
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  AgdaAny
du_1'35'_148 v0
  = coe
      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
      (coe v0)
-- Algebra.Solver.Ring.Lemmas.lemma₀
d_lemma'8320'_260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lemma'8320'_260 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 v8 v9 v10
  = du_lemma'8320'_260 v5 v7 v8 v9 v10
du_lemma'8320'_260 ::
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_lemma'8320'_260 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v5 v6 v7 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v7)
      (coe
         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
         v0
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
               v0 v1 v2)
            v4)
         v3)
      (coe
         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
         v0
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
            v0 v1 v4)
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0 v2 v4)
            v3))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v5
                         = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                             (coe v0) in
                   coe
                     (let v6
                            = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                (coe v5) in
                      coe
                        (let v7
                               = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v6) in
                         coe
                           (let v8
                                  = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                      (coe v7) in
                            coe
                              (let v9
                                     = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                         (coe v8) in
                               coe
                                 (let v10
                                        = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v9) in
                                  coe
                                    (let v11
                                           = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                               (coe v10) in
                                     coe
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.du_setoid_200
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                             (coe v11)))))))))))))
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                  v0 v1 v2)
               v4)
            v3)
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v1 v4)
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v2 v4))
            v3)
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0 v1 v4)
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v2 v4)
               v3))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v5
                            = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                (coe v0) in
                      coe
                        (let v6
                               = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                   (coe v5) in
                         coe
                           (let v7
                                  = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v6) in
                            coe
                              (let v8
                                     = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                         (coe v7) in
                               coe
                                 (let v9
                                        = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                            (coe v8) in
                                  coe
                                    (let v10
                                           = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                               (coe v9) in
                                     coe
                                       (let v11
                                              = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                  (coe v10) in
                                        coe
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.du_setoid_200
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                (coe v11)))))))))))))
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v1 v4)
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v2 v4))
               v3)
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v1 v4)
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v2 v4)
                  v3))
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v1 v4)
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v2 v4)
                  v3))
            (let v5
                   = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                       (coe
                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                          (let v5
                                 = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                     (coe v0) in
                           coe
                             (let v6
                                    = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                        (coe v5) in
                              coe
                                (let v7
                                       = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                           (coe v6) in
                                 coe
                                   (let v8
                                          = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                              (coe v7) in
                                    coe
                                      (let v9
                                             = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                 (coe v8) in
                                       coe
                                         (let v10
                                                = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                    (coe v9) in
                                          coe
                                            (let v11
                                                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                       (coe v10) in
                                             coe
                                               (coe
                                                  MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                  (coe
                                                     MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                     (coe v11))))))))))) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                     (coe v5))
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v1 v4)
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v2 v4)
                        v3))))
            (coe
               MAlonzo.Code.Algebra.Structures.d_assoc_480
               (MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                    (coe v0))))))))
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v1 v4)
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v2 v4)
               v3))
         (coe
            MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
            (let v5
                   = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                       (coe v0) in
             coe
               (let v6
                      = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                          (coe v5) in
                coe
                  (let v7
                         = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v6) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_distrib'691'_1518
                        (MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                           (coe v7))
                        v4 v1 v2))))
            (coe
               MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
               (MAlonzo.Code.Algebra.Structures.d_isMagma_478
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
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                       (coe v0)))))))))
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                     v0 v1 v2)
                  v4)
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v1 v4)
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v2 v4))
               v3 v3)
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
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                          (coe v0))))))))))
               v3)))
-- Algebra.Solver.Ring.Lemmas.lemma₁
d_lemma'8321'_280 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lemma'8321'_280 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 v8 v9 v10 v11
  = du_lemma'8321'_280 v5 v7 v8 v9 v10 v11
du_lemma'8321'_280 ::
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_lemma'8321'_280 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v6 v7 v8 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v8)
      (coe
         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
         v0
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
               v0 v1 v2)
            v5)
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
            v0 v3 v4))
      (coe
         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
         v0
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0 v1 v5)
            v3)
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0 v2 v5)
            v4))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v6
                         = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                             (coe v0) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                (coe v6) in
                      coe
                        (let v8
                               = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v7) in
                         coe
                           (let v9
                                  = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                      (coe v8) in
                            coe
                              (let v10
                                     = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                         (coe v9) in
                               coe
                                 (let v11
                                        = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                            (coe v10) in
                                  coe
                                    (let v12
                                           = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                               (coe v11) in
                                     coe
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.du_setoid_200
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                             (coe v12)))))))))))))
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                  v0 v1 v2)
               v5)
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
               v0 v3 v4))
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0 v1 v5)
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v2 v5)
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                  v0 v3 v4)))
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v1 v5)
               v3)
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v2 v5)
               v4))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v6
                            = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                (coe v0) in
                      coe
                        (let v7
                               = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                   (coe v6) in
                         coe
                           (let v8
                                  = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v7) in
                            coe
                              (let v9
                                     = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                         (coe v8) in
                               coe
                                 (let v10
                                        = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                            (coe v9) in
                                  coe
                                    (let v11
                                           = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                               (coe v10) in
                                     coe
                                       (let v12
                                              = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                  (coe v11) in
                                        coe
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.du_setoid_200
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                (coe v12)))))))))))))
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v1 v5)
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v2 v5)
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                     v0 v3 v4)))
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v1 v5)
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v2 v5)
                     v3)
                  v4))
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v1 v5)
                  v3)
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v2 v5)
                  v4))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v6
                               = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                   (coe v0) in
                         coe
                           (let v7
                                  = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                      (coe v6) in
                            coe
                              (let v8
                                     = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v7) in
                               coe
                                 (let v9
                                        = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                            (coe v8) in
                                  coe
                                    (let v10
                                           = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                               (coe v9) in
                                     coe
                                       (let v11
                                              = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                  (coe v10) in
                                        coe
                                          (let v12
                                                 = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                     (coe v11) in
                                           coe
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                (coe
                                                   MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                   (coe v12)))))))))))))
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v1 v5)
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v2 v5)
                        v3)
                     v4))
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v1 v5)
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                        v0 v3
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v2 v5))
                     v4))
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v1 v5)
                     v3)
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v2 v5)
                     v4))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (let v6
                                  = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                      (coe v0) in
                            coe
                              (let v7
                                     = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                         (coe v6) in
                               coe
                                 (let v8
                                        = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                            (coe v7) in
                                  coe
                                    (let v9
                                           = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                               (coe v8) in
                                     coe
                                       (let v10
                                              = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                  (coe v9) in
                                        coe
                                          (let v11
                                                 = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                     (coe v10) in
                                           coe
                                             (let v12
                                                    = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                        (coe v11) in
                                              coe
                                                (coe
                                                   MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                   (coe
                                                      MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                      (coe v12)))))))))))))
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v1 v5)
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                           v0 v3
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v2 v5))
                        v4))
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v1 v5)
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                        v0 v3
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v2 v5)
                           v4)))
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v1 v5)
                        v3)
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v2 v5)
                        v4))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                              (let v6
                                     = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                         (coe v0) in
                               coe
                                 (let v7
                                        = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                            (coe v6) in
                                  coe
                                    (let v8
                                           = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                               (coe v7) in
                                     coe
                                       (let v9
                                              = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                  (coe v8) in
                                        coe
                                          (let v10
                                                 = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                     (coe v9) in
                                           coe
                                             (let v11
                                                    = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                        (coe v10) in
                                              coe
                                                (let v12
                                                       = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                           (coe v11) in
                                                 coe
                                                   (coe
                                                      MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                      (coe
                                                         MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                         (coe v12)))))))))))))
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v1 v5)
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                           v0 v3
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                              v0
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0 v2 v5)
                              v4)))
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v1 v5)
                           v3)
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v2 v5)
                           v4))
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v1 v5)
                           v3)
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v2 v5)
                           v4))
                     (let v6
                            = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                (coe
                                   MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                   (let v6
                                          = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                              (coe v0) in
                                    coe
                                      (let v7
                                             = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                 (coe v6) in
                                       coe
                                         (let v8
                                                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                    (coe v7) in
                                          coe
                                            (let v9
                                                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                       (coe v8) in
                                             coe
                                               (let v10
                                                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                          (coe v9) in
                                                coe
                                                  (let v11
                                                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                             (coe v10) in
                                                   coe
                                                     (let v12
                                                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                (coe v11) in
                                                      coe
                                                        (coe
                                                           MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                           (coe
                                                              MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                              (coe v12))))))))))) in
                      coe
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                              (coe v6))
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                              v0
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v1 v5)
                                 v3)
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v2 v5)
                                 v4))))
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_sym_36
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
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                (coe
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                   (coe v0))))))))))
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                              v0
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0 v1 v5)
                              v3)
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                              v0
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0 v2 v5)
                              v4))
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v1 v5)
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                              v0 v3
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v2 v5)
                                 v4)))
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_assoc_480
                           (MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                (coe v0))))))))
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v1 v5)
                           v3
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                              v0
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0 v2 v5)
                              v4))))
                  (coe
                     MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
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
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                (coe
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                   (coe v0))))))))))
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v1 v5))
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                        (MAlonzo.Code.Algebra.Structures.d_isMagma_478
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
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                (coe v0)))))))))
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v1 v5)
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v1 v5)
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                              v0 v3
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0 v2 v5))
                           v4)
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                           v0 v3
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                              v0
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0 v2 v5)
                              v4)))
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_assoc_480
                        (MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                             (coe v0))))))))
                        v3
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v2 v5)
                        v4)))
               (coe
                  MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
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
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                (coe v0))))))))))
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v1 v5))
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                     (MAlonzo.Code.Algebra.Structures.d_isMagma_478
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
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                             (coe v0)))))))))
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v1 v5)
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v1 v5)
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v2 v5)
                           v3)
                        v4)
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                           v0 v3
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v2 v5))
                        v4))
                  (coe
                     MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_comm_746
                        (MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                       (coe v0))))))
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v2 v5)
                        v3)
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                        (MAlonzo.Code.Algebra.Structures.d_isMagma_478
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
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                (coe v0)))))))))
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v2 v5)
                           v3)
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                           v0 v3
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v2 v5))
                        v4 v4)
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
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                (coe
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                   (coe v0))))))))))
                        v4))))
            (coe
               MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
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
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                             (coe v0))))))))))
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v1 v5))
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                  (MAlonzo.Code.Algebra.Structures.d_isMagma_478
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
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                          (coe v0)))))))))
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v1 v5)
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v1 v5)
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v2 v5)
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                        v0 v3 v4))
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v2 v5)
                        v3)
                     v4))
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_sym_36
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
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                             (coe v0))))))))))
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v2 v5)
                        v3)
                     v4)
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v2 v5)
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                        v0 v3 v4))
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_assoc_480
                     (MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                          (coe v0))))))))
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v2 v5)
                     v3 v4))))
         (coe
            du_lemma'8320'_260 (coe v0) (coe v1) (coe v2)
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
               v0 v3 v4)
            (coe v5)))
-- Algebra.Solver.Ring.Lemmas.lemma₂
d_lemma'8322'_300 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lemma'8322'_300 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 v8 v9 v10
  = du_lemma'8322'_300 v5 v7 v8 v9 v10
du_lemma'8322'_300 ::
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_lemma'8322'_300 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v5 v6 v7 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v7)
      (coe
         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
         v0
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0 v1 v3)
            v4)
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
            v0 v2 v3))
      (coe
         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
         v0
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0 v1 v4)
            v2)
         v3)
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v5
                         = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                             (coe v0) in
                   coe
                     (let v6
                            = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                (coe v5) in
                      coe
                        (let v7
                               = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v6) in
                         coe
                           (let v8
                                  = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                      (coe v7) in
                            coe
                              (let v9
                                     = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                         (coe v8) in
                               coe
                                 (let v10
                                        = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v9) in
                                  coe
                                    (let v11
                                           = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                               (coe v10) in
                                     coe
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.du_setoid_200
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                             (coe v11)))))))))))))
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v1 v3)
               v4)
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0 v2 v3))
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v1 v4)
               v3)
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0 v2 v3))
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v1 v4)
               v2)
            v3)
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v5
                            = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                (coe v0) in
                      coe
                        (let v6
                               = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                   (coe v5) in
                         coe
                           (let v7
                                  = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v6) in
                            coe
                              (let v8
                                     = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                         (coe v7) in
                               coe
                                 (let v9
                                        = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                            (coe v8) in
                                  coe
                                    (let v10
                                           = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                               (coe v9) in
                                     coe
                                       (let v11
                                              = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                  (coe v10) in
                                        coe
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.du_setoid_200
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                (coe v11)))))))))))))
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v1 v4)
                  v3)
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v2 v3))
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v1 v4)
                  v2)
               v3)
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v1 v4)
                  v2)
               v3)
            (let v5
                   = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                       (coe
                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                          (let v5
                                 = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                     (coe v0) in
                           coe
                             (let v6
                                    = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                        (coe v5) in
                              coe
                                (let v7
                                       = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                           (coe v6) in
                                 coe
                                   (let v8
                                          = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                              (coe v7) in
                                    coe
                                      (let v9
                                             = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                 (coe v8) in
                                       coe
                                         (let v10
                                                = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                    (coe v9) in
                                          coe
                                            (let v11
                                                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                       (coe v10) in
                                             coe
                                               (coe
                                                  MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                  (coe
                                                     MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                     (coe v11))))))))))) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                     (coe v5))
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v1 v4)
                        v2)
                     v3)))
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_36
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
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                          (coe v0))))))))))
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v1 v4)
                     v2)
                  v3)
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v1 v4)
                     v3)
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v2 v3))
               (let v5
                      = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                          (coe v0) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                             (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v6) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_distrib'691'_1518
                           (MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                              (coe v7))
                           v3
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v1 v4)
                           v2))))))
         (coe
            MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
            (coe du_lem_314 (coe v0) (coe v1) (coe v3) (coe v4))
            (coe
               MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
               (MAlonzo.Code.Algebra.Structures.d_isMagma_478
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
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                       (coe v0)))))))))
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v1 v3)
                  v4)
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v1 v4)
                  v3)
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v2 v3)
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v2 v3))
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
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                          (coe v0))))))))))
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v2 v3))))
-- Algebra.Solver.Ring.Lemmas._.lem
d_lem_314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lem_314 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 ~v8 v9 v10
  = du_lem_314 v5 v7 v9 v10
du_lem_314 ::
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_lem_314 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v4 v5 v6 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
      (coe
         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
         v0
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
            v0 v1 v2)
         v3)
      (coe
         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
         v0
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
            v0 v1 v3)
         v2)
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v4
                         = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                             (coe v0) in
                   coe
                     (let v5
                            = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                (coe v4) in
                      coe
                        (let v6
                               = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v5) in
                         coe
                           (let v7
                                  = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                      (coe v6) in
                            coe
                              (let v8
                                     = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                         (coe v7) in
                               coe
                                 (let v9
                                        = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v8) in
                                  coe
                                    (let v10
                                           = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                               (coe v9) in
                                     coe
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.du_setoid_200
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                             (coe v10)))))))))))))
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0 v1 v2)
            v3)
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
            v0 v1
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0 v2 v3))
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0 v1 v3)
            v2)
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v4
                            = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                (coe v0) in
                      coe
                        (let v5
                               = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                   (coe v4) in
                         coe
                           (let v6
                                  = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v5) in
                            coe
                              (let v7
                                     = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                         (coe v6) in
                               coe
                                 (let v8
                                        = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                            (coe v7) in
                                  coe
                                    (let v9
                                           = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                               (coe v8) in
                                     coe
                                       (let v10
                                              = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                  (coe v9) in
                                        coe
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.du_setoid_200
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                (coe v10)))))))))))))
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0 v1
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v2 v3))
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0 v1
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v3 v2))
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v1 v3)
               v2)
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v4
                               = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                   (coe v0) in
                         coe
                           (let v5
                                  = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                      (coe v4) in
                            coe
                              (let v6
                                     = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v5) in
                               coe
                                 (let v7
                                        = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                            (coe v6) in
                                  coe
                                    (let v8
                                           = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                               (coe v7) in
                                     coe
                                       (let v9
                                              = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                  (coe v8) in
                                        coe
                                          (let v10
                                                 = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                     (coe v9) in
                                           coe
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                (coe
                                                   MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                   (coe v10)))))))))))))
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v1
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v3 v2))
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v1 v3)
                  v2)
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v1 v3)
                  v2)
               (let v4
                      = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                          (coe
                             MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                             (let v4
                                    = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                        (coe v0) in
                              coe
                                (let v5
                                       = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                           (coe v4) in
                                 coe
                                   (let v6
                                          = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                              (coe v5) in
                                    coe
                                      (let v7
                                             = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                 (coe v6) in
                                       coe
                                         (let v8
                                                = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                    (coe v7) in
                                          coe
                                            (let v9
                                                   = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                       (coe v8) in
                                             coe
                                               (let v10
                                                      = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                          (coe v9) in
                                                coe
                                                  (coe
                                                     MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                     (coe
                                                        MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                        (coe v10))))))))))) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                        (coe v4))
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v1 v3)
                        v2)))
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_sym_36
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
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                             (coe v0))))))))))
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v1 v3)
                     v2)
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v1
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v3 v2))
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'42''45'assoc_1510
                     (MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                 (coe v0)))))
                     v1 v3 v2)))
            (coe
               MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
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
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                             (coe v0))))))))))
                  v1)
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'42''45'cong_1508
                  (MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                              (coe v0)))))
                  v1 v1
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v2 v3)
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v3 v2))
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'42''45'comm_1712
                  (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                        (coe v0)))
                  v2 v3)))
         (coe
            MAlonzo.Code.Algebra.Structures.d_'42''45'assoc_1510
            (MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                        (coe v0)))))
            v1 v2 v3))
-- Algebra.Solver.Ring.Lemmas.lemma₃
d_lemma'8323'_324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lemma'8323'_324 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 v8 v9 v10
  = du_lemma'8323'_324 v5 v7 v8 v9 v10
du_lemma'8323'_324 ::
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_lemma'8323'_324 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v5 v6 v7 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v7)
      (coe
         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
         v0
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0 v1 v2)
            v4)
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
            v0 v1 v3))
      (coe
         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
         v0 v1
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0 v2 v4)
            v3))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v5
                         = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                             (coe v0) in
                   coe
                     (let v6
                            = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                (coe v5) in
                      coe
                        (let v7
                               = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v6) in
                         coe
                           (let v8
                                  = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                      (coe v7) in
                            coe
                              (let v9
                                     = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                         (coe v8) in
                               coe
                                 (let v10
                                        = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v9) in
                                  coe
                                    (let v11
                                           = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                               (coe v10) in
                                     coe
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.du_setoid_200
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                             (coe v11)))))))))))))
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v1 v2)
               v4)
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0 v1 v3))
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0 v1
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v2 v4))
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0 v1 v3))
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
            v0 v1
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v2 v4)
               v3))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v5
                            = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                (coe v0) in
                      coe
                        (let v6
                               = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                   (coe v5) in
                         coe
                           (let v7
                                  = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v6) in
                            coe
                              (let v8
                                     = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                         (coe v7) in
                               coe
                                 (let v9
                                        = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                            (coe v8) in
                                  coe
                                    (let v10
                                           = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                               (coe v9) in
                                     coe
                                       (let v11
                                              = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                  (coe v10) in
                                        coe
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.du_setoid_200
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                (coe v11)))))))))))))
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v1
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v2 v4))
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v1 v3))
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0 v1
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v2 v4)
                  v3))
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0 v1
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v2 v4)
                  v3))
            (let v5
                   = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                       (coe
                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                          (let v5
                                 = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                     (coe v0) in
                           coe
                             (let v6
                                    = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                        (coe v5) in
                              coe
                                (let v7
                                       = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                           (coe v6) in
                                 coe
                                   (let v8
                                          = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                              (coe v7) in
                                    coe
                                      (let v9
                                             = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                 (coe v8) in
                                       coe
                                         (let v10
                                                = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                    (coe v9) in
                                          coe
                                            (let v11
                                                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                       (coe v10) in
                                             coe
                                               (coe
                                                  MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                  (coe
                                                     MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                     (coe v11))))))))))) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                     (coe v5))
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v1
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v2 v4)
                        v3))))
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_36
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
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                          (coe v0))))))))))
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v1
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v2 v4)
                     v3))
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v1
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v2 v4))
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v1 v3))
               (let v5
                      = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                          (coe v0) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                             (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v6) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_distrib'737'_1516
                           (MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                              (coe v7))
                           v1
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v2 v4)
                           v3))))))
         (coe
            MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
            (coe
               MAlonzo.Code.Algebra.Structures.d_'42''45'assoc_1510
               (MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                           (coe v0)))))
               v1 v2 v4)
            (coe
               MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
               (MAlonzo.Code.Algebra.Structures.d_isMagma_478
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
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                       (coe v0)))))))))
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v1 v2)
                  v4)
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v1
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v2 v4))
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v1 v3)
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v1 v3))
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
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                          (coe v0))))))))))
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v1 v3))))
-- Algebra.Solver.Ring.Lemmas.lemma₄
d_lemma'8324'_344 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lemma'8324'_344 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 v8 v9 v10 v11
  = du_lemma'8324'_344 v5 v7 v8 v9 v10 v11
du_lemma'8324'_344 ::
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_lemma'8324'_344 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v6 v7 v8 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v8)
      (coe
         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
         v0
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v1 v3)
                  v5)
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v1 v4)
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v2 v3)))
            v5)
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
            v0 v2 v4))
      (coe
         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
         v0
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0 v1 v5)
            v2)
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0 v3 v5)
            v4))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v6
                         = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                             (coe v0) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                (coe v6) in
                      coe
                        (let v8
                               = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v7) in
                         coe
                           (let v9
                                  = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                      (coe v8) in
                            coe
                              (let v10
                                     = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                         (coe v9) in
                               coe
                                 (let v11
                                        = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                            (coe v10) in
                                  coe
                                    (let v12
                                           = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                               (coe v11) in
                                     coe
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.du_setoid_200
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                             (coe v12)))))))))))))
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v1 v3)
                     v5)
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v1 v4)
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v2 v3)))
               v5)
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0 v2 v4))
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v1 v3)
                     v5)
                  v5)
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v1 v4)
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v2 v3))
                  v5))
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0 v2 v4))
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v1 v5)
               v2)
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v3 v5)
               v4))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v6
                            = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                (coe v0) in
                      coe
                        (let v7
                               = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                   (coe v6) in
                         coe
                           (let v8
                                  = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v7) in
                            coe
                              (let v9
                                     = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                         (coe v8) in
                               coe
                                 (let v10
                                        = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                            (coe v9) in
                                  coe
                                    (let v11
                                           = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                               (coe v10) in
                                     coe
                                       (let v12
                                              = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                  (coe v11) in
                                        coe
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.du_setoid_200
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                (coe v12)))))))))))))
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v1 v3)
                        v5)
                     v5)
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v1 v4)
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v2 v3))
                     v5))
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v2 v4))
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v1 v3)
                        v5)
                     v5)
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v1 v4)
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v2 v3))
                     v5))
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v2 v4))
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v1 v5)
                  v2)
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v3 v5)
                  v4))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v6
                               = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                   (coe v0) in
                         coe
                           (let v7
                                  = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                      (coe v6) in
                            coe
                              (let v8
                                     = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v7) in
                               coe
                                 (let v9
                                        = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                            (coe v8) in
                                  coe
                                    (let v10
                                           = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                               (coe v9) in
                                     coe
                                       (let v11
                                              = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                  (coe v10) in
                                        coe
                                          (let v12
                                                 = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                     (coe v11) in
                                           coe
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                (coe
                                                   MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                   (coe v12)))))))))))))
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v1 v3)
                           v5)
                        v5)
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v1 v4)
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v2 v3))
                        v5))
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v2 v4))
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v1 v3)
                        v5)
                     v5)
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v1 v4)
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v2 v3))
                        v5)
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v2 v4)))
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v1 v5)
                     v2)
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v3 v5)
                     v4))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (let v6
                                  = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                      (coe v0) in
                            coe
                              (let v7
                                     = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                         (coe v6) in
                               coe
                                 (let v8
                                        = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                            (coe v7) in
                                  coe
                                    (let v9
                                           = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                               (coe v8) in
                                     coe
                                       (let v10
                                              = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                  (coe v9) in
                                        coe
                                          (let v11
                                                 = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                     (coe v10) in
                                           coe
                                             (let v12
                                                    = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                        (coe v11) in
                                              coe
                                                (coe
                                                   MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                   (coe
                                                      MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                      (coe v12)))))))))))))
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v1 v3)
                           v5)
                        v5)
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                              v0
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0 v1 v4)
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0 v2 v3))
                           v5)
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v2 v4)))
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v1 v5)
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v3 v5))
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0 v1 v5)
                              v4)
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v2
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0 v3 v5)))
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v2 v4)))
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v1 v5)
                        v2)
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v3 v5)
                        v4))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                              (let v6
                                     = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                         (coe v0) in
                               coe
                                 (let v7
                                        = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                            (coe v6) in
                                  coe
                                    (let v8
                                           = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                               (coe v7) in
                                     coe
                                       (let v9
                                              = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                  (coe v8) in
                                        coe
                                          (let v10
                                                 = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                     (coe v9) in
                                           coe
                                             (let v11
                                                    = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                        (coe v10) in
                                              coe
                                                (let v12
                                                       = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                           (coe v11) in
                                                 coe
                                                   (coe
                                                      MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                      (coe
                                                         MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                         (coe v12)))))))))))))
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v1 v5)
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v3 v5))
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                              v0
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v1 v5)
                                 v4)
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0 v2
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v3 v5)))
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v2 v4)))
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v1 v5)
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v3 v5))
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0 v1 v5)
                              v4)
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                              v0
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0 v2
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v3 v5))
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0 v2 v4))))
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v1 v5)
                           v2)
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v3 v5)
                           v4))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                 (let v6
                                        = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                            (coe v0) in
                                  coe
                                    (let v7
                                           = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                               (coe v6) in
                                     coe
                                       (let v8
                                              = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                  (coe v7) in
                                        coe
                                          (let v9
                                                 = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                     (coe v8) in
                                           coe
                                             (let v10
                                                    = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                        (coe v9) in
                                              coe
                                                (let v11
                                                       = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                           (coe v10) in
                                                 coe
                                                   (let v12
                                                          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                              (coe v11) in
                                                    coe
                                                      (coe
                                                         MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                         (coe
                                                            MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                            (coe v12)))))))))))))
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0 v1 v5)
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0 v3 v5))
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                              v0
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v1 v5)
                                 v4)
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v2
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v0 v3 v5))
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v2 v4))))
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                              v0
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v1 v5)
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v3 v5))
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v1 v5)
                                 v4))
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                              v0
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0 v2
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v3 v5))
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0 v2 v4)))
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                              v0
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0 v1 v5)
                              v2)
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                              v0
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0 v3 v5)
                              v4))
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                              (coe
                                 MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                    (let v6
                                           = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                               (coe v0) in
                                     coe
                                       (let v7
                                              = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                  (coe v6) in
                                        coe
                                          (let v8
                                                 = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                     (coe v7) in
                                           coe
                                             (let v9
                                                    = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                        (coe v8) in
                                              coe
                                                (let v10
                                                       = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                           (coe v9) in
                                                 coe
                                                   (let v11
                                                          = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                              (coe v10) in
                                                    coe
                                                      (let v12
                                                             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                 (coe v11) in
                                                       coe
                                                         (coe
                                                            MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                            (coe
                                                               MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                               (coe v12)))))))))))))
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                              v0
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v0 v1 v5)
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v0 v3 v5))
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v0 v1 v5)
                                    v4))
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v2
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v0 v3 v5))
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v2 v4)))
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                              v0
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v1 v5)
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                    v0
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v0 v3 v5)
                                    v4))
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0 v2
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                    v0
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v0 v3 v5)
                                    v4)))
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v1 v5)
                                 v2)
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v3 v5)
                                 v4))
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                       (let v6
                                              = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                  (coe v0) in
                                        coe
                                          (let v7
                                                 = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                     (coe v6) in
                                           coe
                                             (let v8
                                                    = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                        (coe v7) in
                                              coe
                                                (let v9
                                                       = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                           (coe v8) in
                                                 coe
                                                   (let v10
                                                          = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                              (coe v9) in
                                                    coe
                                                      (let v11
                                                             = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                 (coe v10) in
                                                       coe
                                                         (let v12
                                                                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                    (coe v11) in
                                                          coe
                                                            (coe
                                                               MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                               (coe
                                                                  MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                  (coe v12)))))))))))))
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v0 v1 v5)
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                       v0
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                          v0 v3 v5)
                                       v4))
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v2
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                       v0
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                          v0 v3 v5)
                                       v4)))
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                    v0
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v0 v1 v5)
                                    v2)
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                    v0
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v0 v3 v5)
                                    v4))
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                    v0
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v0 v1 v5)
                                    v2)
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                    v0
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v0 v3 v5)
                                    v4))
                              (let v6
                                     = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                         (coe
                                            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                            (let v6
                                                   = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                       (coe v0) in
                                             coe
                                               (let v7
                                                      = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                          (coe v6) in
                                                coe
                                                  (let v8
                                                         = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                             (coe v7) in
                                                   coe
                                                     (let v9
                                                            = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                                (coe v8) in
                                                      coe
                                                        (let v10
                                                               = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                                   (coe v9) in
                                                         coe
                                                           (let v11
                                                                  = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                      (coe v10) in
                                                            coe
                                                              (let v12
                                                                     = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                         (coe v11) in
                                                               coe
                                                                 (coe
                                                                    MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                                    (coe
                                                                       MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                       (coe v12))))))))))) in
                               coe
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                       (coe v6))
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v0
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                          v0
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                             v0 v1 v5)
                                          v2)
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                          v0
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                             v0 v3 v5)
                                          v4))))
                              (coe
                                 MAlonzo.Code.Relation.Binary.Structures.d_sym_36
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
                                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                         (coe
                                                            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                            (coe v0))))))))))
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                       v0
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                          v0 v1 v5)
                                       v2)
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                       v0
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                          v0 v3 v5)
                                       v4))
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                    v0
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v0
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                          v0 v1 v5)
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                          v0
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                             v0 v3 v5)
                                          v4))
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v0 v2
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                          v0
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                             v0 v3 v5)
                                          v4)))
                                 (let v6
                                        = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                            (coe v0) in
                                  coe
                                    (let v7
                                           = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                               (coe v6) in
                                     coe
                                       (let v8
                                              = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                  (coe v7) in
                                        coe
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.du_distrib'691'_1518
                                             (MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                (coe v8))
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                                v0
                                                (coe
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                   v0 v3 v5)
                                                v4)
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                v0 v1 v5)
                                             v2))))))
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_sym_36
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
                                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                      (coe
                                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                         (coe v0))))))))))
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v0 v1 v5)
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                       v0
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                          v0 v3 v5)
                                       v4))
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v2
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                       v0
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                          v0 v3 v5)
                                       v4)))
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                    v0
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v0
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                          v0 v1 v5)
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                          v0 v3 v5))
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v0
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                          v0 v1 v5)
                                       v4))
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                    v0
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v0 v2
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                          v0 v3 v5))
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v0 v2 v4)))
                              (coe
                                 MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                                 (let v6
                                        = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                            (coe v0) in
                                  coe
                                    (let v7
                                           = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                               (coe v6) in
                                     coe
                                       (let v8
                                              = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                  (coe v7) in
                                        coe
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.du_distrib'737'_1516
                                             (MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                (coe v8))
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                v0 v1 v5)
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                v0 v3 v5)
                                             v4))))
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                    (MAlonzo.Code.Algebra.Structures.d_isMagma_478
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
                                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                         (coe
                                                            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                            (coe v0)))))))))
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v0
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                          v0 v1 v5)
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                          v0
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                             v0 v3 v5)
                                          v4))
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                       v0
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                          v0
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                             v0 v1 v5)
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                             v0 v3 v5))
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                          v0
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                             v0 v1 v5)
                                          v4))
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v0 v2
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                          v0
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                             v0 v3 v5)
                                          v4))
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                       v0
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                          v0 v2
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                             v0 v3 v5))
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                          v0 v2 v4)))
                                 (let v6
                                        = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                            (coe v0) in
                                  coe
                                    (let v7
                                           = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                               (coe v6) in
                                     coe
                                       (let v8
                                              = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                  (coe v7) in
                                        coe
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.du_distrib'737'_1516
                                             (MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                (coe v8))
                                             v2
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                v0 v3 v5)
                                             v4)))))))
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_sym_36
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
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                   (coe
                                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                      (coe v0))))))))))
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                              v0
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v0 v1 v5)
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v0 v3 v5))
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v0 v1 v5)
                                    v4))
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v2
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v0 v3 v5))
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v2 v4)))
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                              v0
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v1 v5)
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v3 v5))
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v0 v1 v5)
                                    v4)
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                    v0
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v0 v2
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                          v0 v3 v5))
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v0 v2 v4))))
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_assoc_480
                              (MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                (coe
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                   (coe v0))))))))
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v1 v5)
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v3 v5))
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v1 v5)
                                 v4)
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v2
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v0 v3 v5))
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v2 v4)))))
                     (coe
                        MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
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
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                   (coe
                                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                      (coe v0))))))))))
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0 v1 v5)
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0 v3 v5)))
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                           (MAlonzo.Code.Algebra.Structures.d_isMagma_478
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
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                (coe
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                   (coe v0)))))))))
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0 v1 v5)
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0 v3 v5))
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0 v1 v5)
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0 v3 v5))
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                              v0
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v0 v1 v5)
                                    v4)
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v2
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v0 v3 v5)))
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0 v2 v4))
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                              v0
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v1 v5)
                                 v4)
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v2
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v0 v3 v5))
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v2 v4))))
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_assoc_480
                           (MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                (coe v0))))))))
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0 v1 v5)
                              v4)
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v2
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0 v3 v5))
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v2 v4))))
                  (coe
                     MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                     (coe du_lem'8321'_362 (coe v0) (coe v1) (coe v3) (coe v5))
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                        (MAlonzo.Code.Algebra.Structures.d_isMagma_478
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
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                (coe v0)))))))))
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0 v1 v3)
                              v5)
                           v5)
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v1 v5)
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v3 v5))
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v1 v4)
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v2 v3))
                              v5)
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v2 v4))
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                              v0
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v1 v5)
                                 v4)
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0 v2
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v3 v5)))
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v2 v4)))
                     (coe
                        MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                        (coe
                           du_lem'8322'_364 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                           (coe v5))
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                           (MAlonzo.Code.Algebra.Structures.d_isMagma_478
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
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                (coe
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                   (coe v0)))))))))
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v1 v4)
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v2 v3))
                              v5)
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                              v0
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v1 v5)
                                 v4)
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0 v2
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0 v3 v5)))
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v2 v4)
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v2 v4))
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
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                   (coe
                                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                      (coe v0))))))))))
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v2 v4)))))
               (coe
                  MAlonzo.Code.Algebra.Structures.d_assoc_480
                  (MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                       (coe v0))))))))
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v1 v3)
                        v5)
                     v5)
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v1 v4)
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v2 v3))
                     v5)
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v2 v4)))
            (coe
               MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
               (coe
                  MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
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
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                (coe v0))))))))))
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v1 v3)
                           v5)
                        v5))
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                     (MAlonzo.Code.Algebra.Structures.d_isMagma_478
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
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                             (coe v0)))))))))
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v1 v3)
                           v5)
                        v5)
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v1 v3)
                           v5)
                        v5)
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v1 v4)
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v2 v3))
                        v5)
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v1 v4)
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v2 v3))
                        v5))
                  (coe
                     MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                     (coe
                        MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
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
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                   (coe
                                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                      (coe v0))))))))))
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v1 v4))
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                           (MAlonzo.Code.Algebra.Structures.d_isMagma_478
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
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                (coe
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                   (coe v0)))))))))
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v1 v4)
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v1 v4)
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v2 v3)
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v2 v3))
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
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                   (coe
                                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                      (coe v0))))))))))
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v2 v3)))
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_'42''45'cong_1508
                        (MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                    (coe v0)))))
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v1 v4)
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v2 v3))
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v1 v4)
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v2 v3))
                        v5 v5)
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
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                (coe
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                   (coe v0))))))))))
                        v5)))
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                  (MAlonzo.Code.Algebra.Structures.d_isMagma_478
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
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                          (coe v0)))))))))
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v1 v3)
                           v5)
                        v5)
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v1 v4)
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v2 v3))
                        v5))
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v1 v3)
                           v5)
                        v5)
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v1 v4)
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v2 v3))
                        v5))
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v2 v4)
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v2 v4))
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
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                             (coe v0))))))))))
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v2 v4))))
         (coe
            MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
            (let v6
                   = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                       (coe v0) in
             coe
               (let v7
                      = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                          (coe v6) in
                coe
                  (let v8
                         = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v7) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_distrib'691'_1518
                        (MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                           (coe v8))
                        v5
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v1 v3)
                           v5)
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v1 v4)
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v2 v3))))))
            (coe
               MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
               (MAlonzo.Code.Algebra.Structures.d_isMagma_478
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
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                       (coe v0)))))))))
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v1 v3)
                        v5)
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v1 v4)
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v2 v3)))
                  v5)
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v1 v3)
                        v5)
                     v5)
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v1 v4)
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v2 v3))
                     v5))
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v2 v4)
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v2 v4))
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
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                          (coe v0))))))))))
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v2 v4))))
-- Algebra.Solver.Ring.Lemmas._.lem₁′
d_lem'8321''8242'_360 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lem'8321''8242'_360 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 ~v8 v9 ~v10 v11
  = du_lem'8321''8242'_360 v5 v7 v9 v11
du_lem'8321''8242'_360 ::
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_lem'8321''8242'_360 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v4 v5 v6 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
      (coe
         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
         v0
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
            v0 v1 v2)
         v3)
      (coe
         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
         v0
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
            v0 v1 v3)
         v2)
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v4
                         = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                             (coe v0) in
                   coe
                     (let v5
                            = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                (coe v4) in
                      coe
                        (let v6
                               = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v5) in
                         coe
                           (let v7
                                  = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                      (coe v6) in
                            coe
                              (let v8
                                     = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                         (coe v7) in
                               coe
                                 (let v9
                                        = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v8) in
                                  coe
                                    (let v10
                                           = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                               (coe v9) in
                                     coe
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.du_setoid_200
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                             (coe v10)))))))))))))
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0 v1 v2)
            v3)
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
            v0 v1
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0 v2 v3))
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0 v1 v3)
            v2)
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v4
                            = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                (coe v0) in
                      coe
                        (let v5
                               = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                   (coe v4) in
                         coe
                           (let v6
                                  = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v5) in
                            coe
                              (let v7
                                     = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                         (coe v6) in
                               coe
                                 (let v8
                                        = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                            (coe v7) in
                                  coe
                                    (let v9
                                           = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                               (coe v8) in
                                     coe
                                       (let v10
                                              = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                  (coe v9) in
                                        coe
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.du_setoid_200
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                (coe v10)))))))))))))
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0 v1
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v2 v3))
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0 v1
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v3 v2))
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v1 v3)
               v2)
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v4
                               = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                   (coe v0) in
                         coe
                           (let v5
                                  = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                      (coe v4) in
                            coe
                              (let v6
                                     = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v5) in
                               coe
                                 (let v7
                                        = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                            (coe v6) in
                                  coe
                                    (let v8
                                           = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                               (coe v7) in
                                     coe
                                       (let v9
                                              = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                  (coe v8) in
                                        coe
                                          (let v10
                                                 = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                     (coe v9) in
                                           coe
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                (coe
                                                   MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                   (coe v10)))))))))))))
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v1
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v3 v2))
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v1 v3)
                  v2)
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v1 v3)
                  v2)
               (let v4
                      = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                          (coe
                             MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                             (let v4
                                    = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                        (coe v0) in
                              coe
                                (let v5
                                       = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                           (coe v4) in
                                 coe
                                   (let v6
                                          = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                              (coe v5) in
                                    coe
                                      (let v7
                                             = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                 (coe v6) in
                                       coe
                                         (let v8
                                                = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                    (coe v7) in
                                          coe
                                            (let v9
                                                   = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                       (coe v8) in
                                             coe
                                               (let v10
                                                      = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                          (coe v9) in
                                                coe
                                                  (coe
                                                     MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                     (coe
                                                        MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                        (coe v10))))))))))) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                        (coe v4))
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v1 v3)
                        v2)))
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_sym_36
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
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                             (coe v0))))))))))
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v1 v3)
                     v2)
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v1
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v3 v2))
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'42''45'assoc_1510
                     (MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                 (coe v0)))))
                     v1 v3 v2)))
            (coe
               MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
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
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                             (coe v0))))))))))
                  v1)
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'42''45'cong_1508
                  (MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                              (coe v0)))))
                  v1 v1
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v2 v3)
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v3 v2))
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'42''45'comm_1712
                  (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                        (coe v0)))
                  v2 v3)))
         (coe
            MAlonzo.Code.Algebra.Structures.d_'42''45'assoc_1510
            (MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                        (coe v0)))))
            v1 v2 v3))
-- Algebra.Solver.Ring.Lemmas._.lem₁
d_lem'8321'_362 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lem'8321'_362 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 ~v8 v9 ~v10 v11
  = du_lem'8321'_362 v5 v7 v9 v11
du_lem'8321'_362 ::
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_lem'8321'_362 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v4 v5 v6 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
      (coe
         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
         v0
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0 v1 v2)
            v3)
         v3)
      (coe
         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
         v0
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
            v0 v1 v3)
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
            v0 v2 v3))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v4
                         = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                             (coe v0) in
                   coe
                     (let v5
                            = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                (coe v4) in
                      coe
                        (let v6
                               = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v5) in
                         coe
                           (let v7
                                  = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                      (coe v6) in
                            coe
                              (let v8
                                     = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                         (coe v7) in
                               coe
                                 (let v9
                                        = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v8) in
                                  coe
                                    (let v10
                                           = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                               (coe v9) in
                                     coe
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.du_setoid_200
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                             (coe v10)))))))))))))
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v1 v2)
               v3)
            v3)
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v1 v3)
               v2)
            v3)
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0 v1 v3)
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0 v2 v3))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v4
                            = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                (coe v0) in
                      coe
                        (let v5
                               = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                   (coe v4) in
                         coe
                           (let v6
                                  = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v5) in
                            coe
                              (let v7
                                     = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                         (coe v6) in
                               coe
                                 (let v8
                                        = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                            (coe v7) in
                                  coe
                                    (let v9
                                           = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                               (coe v8) in
                                     coe
                                       (let v10
                                              = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                  (coe v9) in
                                        coe
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.du_setoid_200
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                (coe v10)))))))))))))
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v1 v3)
                  v2)
               v3)
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v1 v3)
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v2 v3))
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v1 v3)
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v2 v3))
            (let v4
                   = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                       (coe
                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                          (let v4
                                 = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                     (coe v0) in
                           coe
                             (let v5
                                    = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                        (coe v4) in
                              coe
                                (let v6
                                       = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                           (coe v5) in
                                 coe
                                   (let v7
                                          = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                              (coe v6) in
                                    coe
                                      (let v8
                                             = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                 (coe v7) in
                                       coe
                                         (let v9
                                                = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                    (coe v8) in
                                          coe
                                            (let v10
                                                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                       (coe v9) in
                                             coe
                                               (coe
                                                  MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                  (coe
                                                     MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                     (coe v10))))))))))) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                     (coe v4))
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v1 v3)
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v2 v3))))
            (coe
               MAlonzo.Code.Algebra.Structures.d_'42''45'assoc_1510
               (MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                           (coe v0)))))
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v1 v3)
               v2 v3))
         (coe
            MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
            (coe du_lem'8321''8242'_360 (coe v0) (coe v1) (coe v2) (coe v3))
            (coe
               MAlonzo.Code.Algebra.Structures.d_'42''45'cong_1508
               (MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                           (coe v0)))))
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v1 v2)
                  v3)
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v1 v3)
                  v2)
               v3 v3)
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
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                          (coe v0))))))))))
               v3)))
-- Algebra.Solver.Ring.Lemmas._.lem₂
d_lem'8322'_364 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lem'8322'_364 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 v8 v9 v10 v11
  = du_lem'8322'_364 v5 v7 v8 v9 v10 v11
du_lem'8322'_364 ::
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_lem'8322'_364 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v6 v7 v8 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v8)
      (coe
         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
         v0
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0 v1 v4)
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0 v2 v3))
         v5)
      (coe
         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
         v0
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0 v1 v5)
            v4)
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
            v0 v2
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0 v3 v5)))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v6
                         = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                             (coe v0) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                (coe v6) in
                      coe
                        (let v8
                               = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v7) in
                         coe
                           (let v9
                                  = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                      (coe v8) in
                            coe
                              (let v10
                                     = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                         (coe v9) in
                               coe
                                 (let v11
                                        = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                            (coe v10) in
                                  coe
                                    (let v12
                                           = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                               (coe v11) in
                                     coe
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.du_setoid_200
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                             (coe v12)))))))))))))
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v1 v4)
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v2 v3))
            v5)
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v1 v4)
               v5)
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v2 v3)
               v5))
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v1 v5)
               v4)
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0 v2
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v3 v5)))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v6
                            = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                (coe v0) in
                      coe
                        (let v7
                               = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                   (coe v6) in
                         coe
                           (let v8
                                  = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v7) in
                            coe
                              (let v9
                                     = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                         (coe v8) in
                               coe
                                 (let v10
                                        = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                            (coe v9) in
                                  coe
                                    (let v11
                                           = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                               (coe v10) in
                                     coe
                                       (let v12
                                              = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                  (coe v11) in
                                        coe
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.du_setoid_200
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                (coe v12)))))))))))))
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v1 v4)
                  v5)
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v2 v3)
                  v5))
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v1
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v4 v5))
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v2
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v3 v5)))
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v1 v5)
                  v4)
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0 v2
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v3 v5)))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v6
                               = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                   (coe v0) in
                         coe
                           (let v7
                                  = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                      (coe v6) in
                            coe
                              (let v8
                                     = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v7) in
                               coe
                                 (let v9
                                        = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                            (coe v8) in
                                  coe
                                    (let v10
                                           = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                               (coe v9) in
                                     coe
                                       (let v11
                                              = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                  (coe v10) in
                                        coe
                                          (let v12
                                                 = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                     (coe v11) in
                                           coe
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                (coe
                                                   MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                   (coe v12)))))))))))))
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v1
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v4 v5))
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v2
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v3 v5)))
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v1
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v5 v4))
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v2
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v3 v5)))
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v1 v5)
                     v4)
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v2
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v3 v5)))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (let v6
                                  = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                      (coe v0) in
                            coe
                              (let v7
                                     = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                         (coe v6) in
                               coe
                                 (let v8
                                        = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                            (coe v7) in
                                  coe
                                    (let v9
                                           = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                               (coe v8) in
                                     coe
                                       (let v10
                                              = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                  (coe v9) in
                                        coe
                                          (let v11
                                                 = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                     (coe v10) in
                                           coe
                                             (let v12
                                                    = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                        (coe v11) in
                                              coe
                                                (coe
                                                   MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                   (coe
                                                      MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                      (coe v12)))))))))))))
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v1
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v5 v4))
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v2
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v3 v5)))
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v1 v5)
                        v4)
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v2
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v3 v5)))
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v1 v5)
                        v4)
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v2
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v3 v5)))
                  (let v6
                         = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                             (coe
                                MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                (let v6
                                       = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                           (coe v0) in
                                 coe
                                   (let v7
                                          = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                              (coe v6) in
                                    coe
                                      (let v8
                                             = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                 (coe v7) in
                                       coe
                                         (let v9
                                                = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                    (coe v8) in
                                          coe
                                            (let v10
                                                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                       (coe v9) in
                                             coe
                                               (let v11
                                                      = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                          (coe v10) in
                                                coe
                                                  (let v12
                                                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                             (coe v11) in
                                                   coe
                                                     (coe
                                                        MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                        (coe
                                                           MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                           (coe v12))))))))))) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                           (coe v6))
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0 v1 v5)
                              v4)
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v2
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0 v3 v5)))))
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_sym_36
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
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                (coe v0))))))))))
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v1 v5)
                           v4)
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v2
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v3 v5)))
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                        v0
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v1
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v5 v4))
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v2
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v3 v5)))
                     (coe
                        MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_'42''45'assoc_1510
                           (MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                       (coe v0)))))
                           v1 v5 v4)
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                           (MAlonzo.Code.Algebra.Structures.d_isMagma_478
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
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                (coe
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                   (coe v0)))))))))
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0 v1 v5)
                              v4)
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v1
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0 v5 v4))
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v2
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0 v3 v5))
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v2
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0 v3 v5)))
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
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                   (coe
                                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                      (coe v0))))))))))
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v0 v2
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v0 v3 v5))))))
               (coe
                  MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                  (coe
                     MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
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
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                (coe
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                   (coe v0))))))))))
                        v1)
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_'42''45'cong_1508
                        (MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                    (coe v0)))))
                        v1 v1
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v4 v5)
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v5 v4))
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_'42''45'comm_1712
                        (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                              (coe v0)))
                        v4 v5))
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                     (MAlonzo.Code.Algebra.Structures.d_isMagma_478
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
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                             (coe v0)))))))))
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v1
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v4 v5))
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v1
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v5 v4))
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v2
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v3 v5))
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v2
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v3 v5)))
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
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                (coe v0))))))))))
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v2
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                           v0 v3 v5)))))
            (coe
               MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'42''45'assoc_1510
                  (MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                              (coe v0)))))
                  v1 v4 v5)
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                  (MAlonzo.Code.Algebra.Structures.d_isMagma_478
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
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                          (coe v0)))))))))
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v1 v4)
                     v5)
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v1
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v4 v5))
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v2 v3)
                     v5)
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0 v2
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v3 v5)))
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'42''45'assoc_1510
                  (MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                              (coe v0)))))
                  v2 v3 v5)))
         (let v6
                = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                    (coe v0) in
          coe
            (let v7
                   = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                       (coe v6) in
             coe
               (let v8
                      = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v7) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_distrib'691'_1518
                     (MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                        (coe v8))
                     v5
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v1 v4)
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0 v2 v3))))))
-- Algebra.Solver.Ring.Lemmas.lemma₅
d_lemma'8325'_368 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny
d_lemma'8325'_368 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7
  = du_lemma'8325'_368 v5 v7
du_lemma'8325'_368 ::
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny
du_lemma'8325'_368 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v4)
      (coe
         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
         v0
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0
                  (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                     (coe v0))
                  v1)
               (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                  (coe v0)))
            v1)
         (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
            (coe v0)))
      v1
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v2
                         = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                             (coe v0) in
                   coe
                     (let v3
                            = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                (coe v2) in
                      coe
                        (let v4
                               = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v3) in
                         coe
                           (let v5
                                  = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                      (coe v4) in
                            coe
                              (let v6
                                     = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                         (coe v5) in
                               coe
                                 (let v7
                                        = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v6) in
                                  coe
                                    (let v8
                                           = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                               (coe v7) in
                                     coe
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.du_setoid_200
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                             (coe v8)))))))))))))
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0
                     (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                        (coe v0))
                     v1)
                  (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                     (coe v0)))
               v1)
            (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
               (coe v0)))
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                  v0
                  (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                     (coe v0))
                  (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                     (coe v0)))
               v1)
            (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
               (coe v0)))
         v1
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v2
                            = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                (coe v0) in
                      coe
                        (let v3
                               = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                   (coe v2) in
                         coe
                           (let v4
                                  = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v3) in
                            coe
                              (let v5
                                     = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                         (coe v4) in
                               coe
                                 (let v6
                                        = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                            (coe v5) in
                                  coe
                                    (let v7
                                           = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                               (coe v6) in
                                     coe
                                       (let v8
                                              = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                  (coe v7) in
                                        coe
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.du_setoid_200
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                (coe v8)))))))))))))
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                     v0
                     (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                        (coe v0))
                     (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                        (coe v0)))
                  v1)
               (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                  (coe v0)))
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0
                  (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                     (coe v0))
                  v1)
               (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                  (coe v0)))
            v1
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v2
                               = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                   (coe v0) in
                         coe
                           (let v3
                                  = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                      (coe v2) in
                            coe
                              (let v4
                                     = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v3) in
                               coe
                                 (let v5
                                        = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                            (coe v4) in
                                  coe
                                    (let v6
                                           = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                               (coe v5) in
                                     coe
                                       (let v7
                                              = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                  (coe v6) in
                                        coe
                                          (let v8
                                                 = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                     (coe v7) in
                                           coe
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                (coe
                                                   MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                   (coe v8)))))))))))))
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0
                     (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                        (coe v0))
                     v1)
                  (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                     (coe v0)))
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0
                  (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                     (coe v0))
                  v1)
               v1
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (let v2
                                  = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                      (coe v0) in
                            coe
                              (let v3
                                     = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                         (coe v2) in
                               coe
                                 (let v4
                                        = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                            (coe v3) in
                                  coe
                                    (let v5
                                           = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                               (coe v4) in
                                     coe
                                       (let v6
                                              = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                  (coe v5) in
                                        coe
                                          (let v7
                                                 = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                     (coe v6) in
                                           coe
                                             (let v8
                                                    = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                        (coe v7) in
                                              coe
                                                (coe
                                                   MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                   (coe
                                                      MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                      (coe v8)))))))))))))
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0
                     (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                        (coe v0))
                     v1)
                  v1 v1
                  (let v2
                         = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                             (coe
                                MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                (let v2
                                       = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                           (coe v0) in
                                 coe
                                   (let v3
                                          = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                              (coe v2) in
                                    coe
                                      (let v4
                                             = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                 (coe v3) in
                                       coe
                                         (let v5
                                                = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                    (coe v4) in
                                          coe
                                            (let v6
                                                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                       (coe v5) in
                                             coe
                                               (let v7
                                                      = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                          (coe v6) in
                                                coe
                                                  (let v8
                                                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                             (coe v7) in
                                                   coe
                                                     (coe
                                                        MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                        (coe
                                                           MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                           (coe v8))))))))))) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                           (coe v2))
                        (coe v1)))
                  (let v2
                         = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                             (coe v0) in
                   coe
                     (let v3
                            = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                (coe v2) in
                      coe
                        (let v4
                               = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v3) in
                         coe
                           (let v5
                                  = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                      (coe v4) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_identity'737'_724
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1568
                                    (coe v5))
                                 v1))))))
               (let v2
                      = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                          (coe v0) in
                coe
                  (let v3
                         = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                             (coe v2) in
                   coe
                     (let v4
                            = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v3) in
                      coe
                        (let v5
                               = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                   (coe v4) in
                         coe
                           (let v6
                                  = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                      (coe v5) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_identity'691'_726
                                 (MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v6))
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v0
                                    (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                                       (coe v0))
                                    v1))))))))
            (coe
               MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
               (coe
                  MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                  (let v2
                         = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                             (coe v0) in
                   coe
                     (let v3
                            = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                (coe v2) in
                      coe
                        (let v4
                               = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v3) in
                         coe
                           (let v5
                                  = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                      (coe v4) in
                            coe
                              (let v6
                                     = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                         (coe v5) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.du_identity'737'_724
                                    (MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v6))
                                    (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                                       (coe v0))))))))
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'42''45'cong_1508
                     (MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                 (coe v0)))))
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                        v0
                        (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                           (coe v0))
                        (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                           (coe v0)))
                     (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                        (coe v0))
                     v1 v1)
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
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                (coe v0))))))))))
                     v1))
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                  (MAlonzo.Code.Algebra.Structures.d_isMagma_478
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
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                          (coe v0)))))))))
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                        v0
                        (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                           (coe v0))
                        (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                           (coe v0)))
                     v1)
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                     v0
                     (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                        (coe v0))
                     v1)
                  (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                     (coe v0))
                  (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                     (coe v0)))
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
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                             (coe v0))))))))))
                  (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                     (coe v0)))))
         (coe
            MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
            (coe
               MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
               (coe
                  MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                  (let v2
                         = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                             (coe v0) in
                   coe
                     (let v3
                            = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                (coe v2) in
                      coe
                        (let v4
                               = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v3) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_zero'737'_1378
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1678
                                 (coe v4))
                              v1))))
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                     (MAlonzo.Code.Algebra.Structures.d_isMagma_478
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
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                             (coe v0)))))))))
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0
                        (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                           (coe v0))
                        v1)
                     (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                        (coe v0))
                     (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                        (coe v0))
                     (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                        (coe v0)))
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
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                (coe v0))))))))))
                     (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                        (coe v0))))
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'42''45'cong_1508
                  (MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                        (coe
                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                              (coe v0)))))
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0
                        (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                           (coe v0))
                        v1)
                     (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                        (coe v0)))
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                     v0
                     (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                        (coe v0))
                     (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                        (coe v0)))
                  v1 v1)
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
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                             (coe v0))))))))))
                  v1))
            (coe
               MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
               (MAlonzo.Code.Algebra.Structures.d_isMagma_478
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
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                       (coe v0)))))))))
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                     v0
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                        v0
                        (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                           (coe v0))
                        v1)
                     (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                        (coe v0)))
                  v1)
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                     v0
                     (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                        (coe v0))
                     (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                        (coe v0)))
                  v1)
               (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                  (coe v0))
               (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                  (coe v0)))
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
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                          (coe v0))))))))))
               (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                  (coe v0)))))
-- Algebra.Solver.Ring.Lemmas.lemma₆
d_lemma'8326'_376 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_lemma'8326'_376 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 v8
  = du_lemma'8326'_376 v5 v7 v8
du_lemma'8326'_376 ::
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_lemma'8326'_376 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v3 v4 v5 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v5)
      (coe
         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
         v0
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
            v0
            (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
               (coe v0))
            v2)
         v1)
      v1
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v3
                         = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                             (coe v0) in
                   coe
                     (let v4
                            = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                (coe v3) in
                      coe
                        (let v5
                               = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v4) in
                         coe
                           (let v6
                                  = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                      (coe v5) in
                            coe
                              (let v7
                                     = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                         (coe v6) in
                               coe
                                 (let v8
                                        = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v7) in
                                  coe
                                    (let v9
                                           = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                               (coe v8) in
                                     coe
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.du_setoid_200
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                             (coe v9)))))))))))))
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0
               (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                  (coe v0))
               v2)
            v1)
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
            v0
            (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
               (coe v0))
            v1)
         v1
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v3
                            = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                (coe v0) in
                      coe
                        (let v4
                               = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                   (coe v3) in
                         coe
                           (let v5
                                  = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v4) in
                            coe
                              (let v6
                                     = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                         (coe v5) in
                               coe
                                 (let v7
                                        = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                            (coe v6) in
                                  coe
                                    (let v8
                                           = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                               (coe v7) in
                                     coe
                                       (let v9
                                              = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                  (coe v8) in
                                        coe
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.du_setoid_200
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                (coe v9)))))))))))))
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
               v0
               (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                  (coe v0))
               v1)
            v1 v1
            (let v3
                   = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                       (coe
                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                          (let v3
                                 = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                     (coe v0) in
                           coe
                             (let v4
                                    = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                        (coe v3) in
                              coe
                                (let v5
                                       = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                           (coe v4) in
                                 coe
                                   (let v6
                                          = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                              (coe v5) in
                                    coe
                                      (let v7
                                             = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                 (coe v6) in
                                       coe
                                         (let v8
                                                = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                    (coe v7) in
                                          coe
                                            (let v9
                                                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                       (coe v8) in
                                             coe
                                               (coe
                                                  MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                  (coe
                                                     MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                     (coe v9))))))))))) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                     (coe v3))
                  (coe v1)))
            (let v3
                   = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                       (coe v0) in
             coe
               (let v4
                      = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                          (coe v3) in
                coe
                  (let v5
                         = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v4) in
                   coe
                     (let v6
                            = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                (coe v5) in
                      coe
                        (let v7
                               = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                   (coe v6) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_identity'737'_724
                              (MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v7)) v1)))))))
         (coe
            MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
            (let v3
                   = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                       (coe v0) in
             coe
               (let v4
                      = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                          (coe v3) in
                coe
                  (let v5
                         = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_zero'737'_1378
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1678
                           (coe v5))
                        v2))))
            (coe
               MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
               (MAlonzo.Code.Algebra.Structures.d_isMagma_478
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
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                       (coe v0)))))))))
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0
                  (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                     (coe v0))
                  v2)
               (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                  (coe v0))
               v1 v1)
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
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                          (coe v0))))))))))
               v1)))
-- Algebra.Solver.Ring.Lemmas.lemma₇
d_lemma'8327'_384 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny
d_lemma'8327'_384 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7
  = du_lemma'8327'_384 v5 v7
du_lemma'8327'_384 ::
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny
du_lemma'8327'_384 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v4)
      (coe
         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
         v0
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'45'__208
            v0
            (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
               (coe v0)))
         v1)
      (coe
         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'45'__208
         v0 v1)
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v2
                         = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                             (coe v0) in
                   coe
                     (let v3
                            = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                (coe v2) in
                      coe
                        (let v4
                               = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v3) in
                         coe
                           (let v5
                                  = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                      (coe v4) in
                            coe
                              (let v6
                                     = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                         (coe v5) in
                               coe
                                 (let v7
                                        = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v6) in
                                  coe
                                    (let v8
                                           = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                               (coe v7) in
                                     coe
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.du_setoid_200
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                             (coe v8)))))))))))))
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'45'__208
               v0
               (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                  (coe v0)))
            v1)
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'45'__208
            v0
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
               v0
               (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                  (coe v0))
               v1))
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'45'__208
            v0 v1)
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v2
                            = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                (coe v0) in
                      coe
                        (let v3
                               = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                   (coe v2) in
                         coe
                           (let v4
                                  = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v3) in
                            coe
                              (let v5
                                     = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                         (coe v4) in
                               coe
                                 (let v6
                                        = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                            (coe v5) in
                                  coe
                                    (let v7
                                           = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                               (coe v6) in
                                     coe
                                       (let v8
                                              = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                  (coe v7) in
                                        coe
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.du_setoid_200
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                (coe v8)))))))))))))
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'45'__208
               v0
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0
                  (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                     (coe v0))
                  v1))
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'45'__208
               v0 v1)
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'45'__208
               v0 v1)
            (let v2
                   = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                       (coe
                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                          (let v2
                                 = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                     (coe v0) in
                           coe
                             (let v3
                                    = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                        (coe v2) in
                              coe
                                (let v4
                                       = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                           (coe v3) in
                                 coe
                                   (let v5
                                          = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                              (coe v4) in
                                    coe
                                      (let v6
                                             = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                 (coe v5) in
                                       coe
                                         (let v7
                                                = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                    (coe v6) in
                                          coe
                                            (let v8
                                                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                       (coe v7) in
                                             coe
                                               (coe
                                                  MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                  (coe
                                                     MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                     (coe v8))))))))))) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                     (coe v2))
                  (coe
                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'45'__208
                     v0 v1)))
            (coe
               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'45''8255'cong_64
               (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                  (coe v0))
               (coe
                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                  v0
                  (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                     (coe v0))
                  v1)
               v1
               (let v2
                      = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                          (coe v0) in
                coe
                  (let v3
                         = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                             (coe v2) in
                   coe
                     (let v4
                            = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v3) in
                      coe
                        (let v5
                               = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                   (coe v4) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_identity'737'_724
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1568 (coe v5))
                              v1)))))))
         (coe
            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'45''8255''42''45'distrib'737'_70
            (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
               (coe v0))
            (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
               (coe v0))
            v1))
