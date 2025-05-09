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

module MAlonzo.Code.Algebra.Properties.Group where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Algebra.Bundles qualified
import MAlonzo.Code.Algebra.Consequences.Setoid qualified
import MAlonzo.Code.Algebra.Properties.Loop qualified
import MAlonzo.Code.Algebra.Properties.QQuasigroup qualified
import MAlonzo.Code.Algebra.Structures qualified
import MAlonzo.Code.Function.Base qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Reasoning.Base.Single qualified
import MAlonzo.Code.Relation.Binary.Reasoning.Syntax qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Algebra.Properties.Group._._//_
d__'47''47'__16 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'47''47'__16 ~v0 ~v1 v2 = du__'47''47'__16 v2
du__'47''47'__16 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'47''47'__16 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du__'47''47'__1098
      (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
      (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
-- Algebra.Properties.Group._._\\_
d__'92''92'__18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'92''92'__18 ~v0 ~v1 v2 = du__'92''92'__18 v2
du__'92''92'__18 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'92''92'__18 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du__'92''92'__1092
      (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
      (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
-- Algebra.Properties.Group._.Commutative
d_Commutative_264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Commutative_264 = erased
-- Algebra.Properties.Group._.Congruent₂
d_Congruent'8322'_268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Congruent'8322'_268 = erased
-- Algebra.Properties.Group._.Involutive
d_Involutive_288 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  (AgdaAny -> AgdaAny) -> ()
d_Involutive_288 = erased
-- Algebra.Properties.Group._.LeftDivides
d_LeftDivides_300 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftDivides_300 = erased
-- Algebra.Properties.Group._.LeftDividesʳ
d_LeftDivides'691'_302 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftDivides'691'_302 = erased
-- Algebra.Properties.Group._.LeftDividesˡ
d_LeftDivides'737'_304 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftDivides'737'_304 = erased
-- Algebra.Properties.Group._.RightDivides
d_RightDivides_330 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightDivides_330 = erased
-- Algebra.Properties.Group._.RightDividesʳ
d_RightDivides'691'_332 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightDivides'691'_332 = erased
-- Algebra.Properties.Group._.RightDividesˡ
d_RightDivides'737'_334 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightDivides'737'_334 = erased
-- Algebra.Properties.Group._.SelfInverse
d_SelfInverse_348 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  (AgdaAny -> AgdaAny) -> ()
d_SelfInverse_348 = erased
-- Algebra.Properties.Group._.IsLoop
d_IsLoop_368 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Properties.Group._.IsQuasigroup
d_IsQuasigroup_370 a0 a1 a2 a3 a4 a5 = ()
-- Algebra.Properties.Group._.IsLoop.identity
d_identity_386 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3026 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_386 v0
  = coe MAlonzo.Code.Algebra.Structures.d_identity_3042 (coe v0)
-- Algebra.Properties.Group._.IsLoop.isQuasigroup
d_isQuasigroup_398 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3026 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2944
d_isQuasigroup_398 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040 (coe v0)
-- Algebra.Properties.Group._.IsQuasigroup.//-cong
d_'47''47''45'cong_430 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2944 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong_430 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'47''47''45'cong_2966 (coe v0)
-- Algebra.Properties.Group._.IsQuasigroup.\\-cong
d_'92''92''45'cong_436 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2944 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong_436 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'92''92''45'cong_2964 (coe v0)
-- Algebra.Properties.Group._.IsQuasigroup.isMagma
d_isMagma_444 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2944 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_444 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_2962 (coe v0)
-- Algebra.Properties.Group._.IsQuasigroup.leftDivides
d_leftDivides_448 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2944 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_448 v0
  = coe MAlonzo.Code.Algebra.Structures.d_leftDivides_2968 (coe v0)
-- Algebra.Properties.Group._.IsQuasigroup.rightDivides
d_rightDivides_458 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2944 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_458 v0
  = coe MAlonzo.Code.Algebra.Structures.d_rightDivides_2970 (coe v0)
-- Algebra.Properties.Group.\\-cong₂
d_'92''92''45'cong'8322'_516 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong'8322'_516 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8
  = du_'92''92''45'cong'8322'_516 v2 v3 v4 v5 v6 v7 v8
du_'92''92''45'cong'8322'_516 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'92''92''45'cong'8322'_516 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
      (MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
               (coe MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0)))))
      (coe
         MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
         (MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
         (\ v7 v8 -> v7) v1 v2)
      (coe
         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
         (\ v7 v8 -> v8)
         (MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0)) v1 v2)
      v3 v4
      (coe
         MAlonzo.Code.Algebra.Structures.d_'8315''185''45'cong_1054
         (MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0)) v1 v2 v5)
      v6
-- Algebra.Properties.Group.//-cong₂
d_'47''47''45'cong'8322'_522 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong'8322'_522 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8
  = du_'47''47''45'cong'8322'_522 v2 v3 v4 v5 v6 v7 v8
du_'47''47''45'cong'8322'_522 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'47''47''45'cong'8322'_522 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
      (MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
               (coe MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0)))))
      v1 v2
      (coe
         MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
         (MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
         (\ v7 v8 -> v7) v3 v4)
      (coe
         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
         (\ v7 v8 -> v8)
         (MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0)) v3 v4)
      v5
      (coe
         MAlonzo.Code.Algebra.Structures.d_'8315''185''45'cong_1054
         (MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0)) v3 v4 v6)
-- Algebra.Properties.Group.\\-leftDividesˡ
d_'92''92''45'leftDivides'737'_528 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'leftDivides'737'_528 ~v0 ~v1 v2 v3 v4
  = du_'92''92''45'leftDivides'737'_528 v2 v3 v4
du_'92''92''45'leftDivides'737'_528 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'92''92''45'leftDivides'737'_528 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v3 v4 v5 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v5)
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v1
         (coe
            MAlonzo.Code.Algebra.Structures.du__'92''92'__1092
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
            (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
            (coe v1) (coe v2)))
      v2
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                   coe
                     (let v4
                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3) in
                      coe
                        (let v5
                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v4) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_setoid_200
                              (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5)))))))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
               (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                coe
                  (let v4
                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3) in
                   coe
                     (let v5
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v4) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_setoid_200
                           (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))))))))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v1
            (coe
               MAlonzo.Code.Algebra.Structures.du__'92''92'__1092
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
               (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
               (coe v1) (coe v2)))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v1
               (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1))
            v2)
         v2
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                      coe
                        (let v4
                               = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3) in
                         coe
                           (let v5
                                  = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v4) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_setoid_200
                                 (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5)))))))))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v1
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1))
               v2)
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
               (MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v0)) v2)
            v2
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                         coe
                           (let v4
                                  = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3) in
                            coe
                              (let v5
                                     = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v4) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.du_setoid_200
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                       (coe v5)))))))))
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
                  (MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v0)) v2)
               v2 v2
               (let v3
                      = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                          (coe
                             MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                             (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                              coe
                                (let v4
                                       = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3) in
                                 coe
                                   (let v5
                                          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
                                              (coe v4) in
                                    coe
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.du_setoid_200
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                            (coe v5))))))) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                        (coe v3))
                     (coe v2)))
               (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_identity'737'_726
                     (MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3)) v2)))
            (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
             coe
               (let v4
                      = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3) in
                coe
                  (let v5
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'691'_206
                        (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))
                        (coe v2)
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v1
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1))
                        (coe MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v0))
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_inverse'691'_1108
                           (MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0)) v1))))))
         (coe
            MAlonzo.Code.Algebra.Structures.d_assoc_482
            (MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
                  (coe MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0))))
            v1 (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1)
            v2))
-- Algebra.Properties.Group.\\-leftDividesʳ
d_'92''92''45'leftDivides'691'_534 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'leftDivides'691'_534 ~v0 ~v1 v2 v3 v4
  = du_'92''92''45'leftDivides'691'_534 v2 v3 v4
du_'92''92''45'leftDivides'691'_534 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'92''92''45'leftDivides'691'_534 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v3 v4 v5 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v5)
      (coe
         MAlonzo.Code.Algebra.Structures.du__'92''92'__1092
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
         (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
         (coe v1)
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v1 v2))
      v2
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                   coe
                     (let v4
                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3) in
                      coe
                        (let v5
                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v4) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_setoid_200
                              (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5)))))))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
               (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                coe
                  (let v4
                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3) in
                   coe
                     (let v5
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v4) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_setoid_200
                           (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))))))))
         (coe
            MAlonzo.Code.Algebra.Structures.du__'92''92'__1092
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
            (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
            (coe v1)
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v1 v2))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
               (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1) v1)
            v2)
         v2
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                      coe
                        (let v4
                               = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3) in
                         coe
                           (let v5
                                  = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v4) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_setoid_200
                                 (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5)))))))))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1) v1)
               v2)
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
               (MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v0)) v2)
            v2
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                         coe
                           (let v4
                                  = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3) in
                            coe
                              (let v5
                                     = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v4) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.du_setoid_200
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                       (coe v5)))))))))
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
                  (MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v0)) v2)
               v2 v2
               (let v3
                      = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                          (coe
                             MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                             (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                              coe
                                (let v4
                                       = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3) in
                                 coe
                                   (let v5
                                          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
                                              (coe v4) in
                                    coe
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.du_setoid_200
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                            (coe v5))))))) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                        (coe v3))
                     (coe v2)))
               (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_identity'737'_726
                     (MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3)) v2)))
            (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
             coe
               (let v4
                      = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3) in
                coe
                  (let v5
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'691'_206
                        (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))
                        (coe v2)
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1) v1)
                        (coe MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v0))
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_inverse'737'_1106
                           (MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0)) v1))))))
         (coe
            MAlonzo.Code.Algebra.Structures.d_assoc_482
            (MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
                  (coe MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0))))
            (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1) v1
            v2))
-- Algebra.Properties.Group.\\-leftDivides
d_'92''92''45'leftDivides_540 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'92''92''45'leftDivides_540 ~v0 ~v1 v2
  = du_'92''92''45'leftDivides_540 v2
du_'92''92''45'leftDivides_540 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'92''92''45'leftDivides_540 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_'92''92''45'leftDivides'737'_528 (coe v0))
      (coe du_'92''92''45'leftDivides'691'_534 (coe v0))
-- Algebra.Properties.Group.//-rightDividesˡ
d_'47''47''45'rightDivides'737'_542 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'rightDivides'737'_542 ~v0 ~v1 v2 v3 v4
  = du_'47''47''45'rightDivides'737'_542 v2 v3 v4
du_'47''47''45'rightDivides'737'_542 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'47''47''45'rightDivides'737'_542 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v3 v4 v5 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v5)
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
         (coe
            MAlonzo.Code.Algebra.Structures.du__'47''47'__1098
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
            (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
            (coe v2) (coe v1))
         v1)
      v2
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                   coe
                     (let v4
                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3) in
                      coe
                        (let v5
                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v4) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_setoid_200
                              (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5)))))))))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
            (coe
               MAlonzo.Code.Algebra.Structures.du__'47''47'__1098
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
               (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
               (coe v2) (coe v1))
            v1)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v2
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
               (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1) v1))
         v2
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                      coe
                        (let v4
                               = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3) in
                         coe
                           (let v5
                                  = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v4) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_setoid_200
                                 (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5)))))))))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v2
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1) v1))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v2
               (MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v0)))
            v2
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                         coe
                           (let v4
                                  = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3) in
                            coe
                              (let v5
                                     = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v4) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.du_setoid_200
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                       (coe v5)))))))))
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v2
                  (MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v0)))
               v2 v2
               (let v3
                      = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                          (coe
                             MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                             (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                              coe
                                (let v4
                                       = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3) in
                                 coe
                                   (let v5
                                          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
                                              (coe v4) in
                                    coe
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.du_setoid_200
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                            (coe v5))))))) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                        (coe v3))
                     (coe v2)))
               (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_identity'691'_728
                     (MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3)) v2)))
            (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
             coe
               (let v4
                      = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3) in
                coe
                  (let v5
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'737'_202
                        (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))
                        (coe v2)
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1) v1)
                        (coe MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v0))
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_inverse'737'_1106
                           (MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0)) v1))))))
         (coe
            MAlonzo.Code.Algebra.Structures.d_assoc_482
            (MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
                  (coe MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0))))
            v2 (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1)
            v1))
-- Algebra.Properties.Group.//-rightDividesʳ
d_'47''47''45'rightDivides'691'_548 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'rightDivides'691'_548 ~v0 ~v1 v2 v3 v4
  = du_'47''47''45'rightDivides'691'_548 v2 v3 v4
du_'47''47''45'rightDivides'691'_548 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'47''47''45'rightDivides'691'_548 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v3 v4 v5 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v5)
      (coe
         MAlonzo.Code.Algebra.Structures.du__'47''47'__1098
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
         (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v2 v1)
         (coe v1))
      v2
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                   coe
                     (let v4
                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3) in
                      coe
                        (let v5
                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v4) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_setoid_200
                              (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5)))))))))
         (coe
            MAlonzo.Code.Algebra.Structures.du__'47''47'__1098
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
            (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v2 v1)
            (coe v1))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v2
            (coe
               MAlonzo.Code.Algebra.Structures.du__'47''47'__1098
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
               (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
               (coe v1) (coe v1)))
         v2
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                      coe
                        (let v4
                               = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3) in
                         coe
                           (let v5
                                  = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v4) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_setoid_200
                                 (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5)))))))))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v2
               (coe
                  MAlonzo.Code.Algebra.Structures.du__'47''47'__1098
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
                  (coe v1) (coe v1)))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v2
               (MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v0)))
            v2
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                         coe
                           (let v4
                                  = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3) in
                            coe
                              (let v5
                                     = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v4) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.du_setoid_200
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                       (coe v5)))))))))
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v2
                  (MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v0)))
               v2 v2
               (let v3
                      = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                          (coe
                             MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                             (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                              coe
                                (let v4
                                       = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3) in
                                 coe
                                   (let v5
                                          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
                                              (coe v4) in
                                    coe
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.du_setoid_200
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                            (coe v5))))))) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                        (coe v3))
                     (coe v2)))
               (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_identity'691'_728
                     (MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3)) v2)))
            (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
             coe
               (let v4
                      = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3) in
                coe
                  (let v5
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'737'_202
                        (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))
                        (coe v2)
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v1
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1))
                        (coe MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v0))
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_inverse'691'_1108
                           (MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0)) v1))))))
         (coe
            MAlonzo.Code.Algebra.Structures.d_assoc_482
            (MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
                  (coe MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0))))
            v2 v1
            (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1)))
-- Algebra.Properties.Group.//-rightDivides
d_'47''47''45'rightDivides_554 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'47''47''45'rightDivides_554 ~v0 ~v1 v2
  = du_'47''47''45'rightDivides_554 v2
du_'47''47''45'rightDivides_554 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'47''47''45'rightDivides_554 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_'47''47''45'rightDivides'737'_542 (coe v0))
      (coe du_'47''47''45'rightDivides'691'_548 (coe v0))
-- Algebra.Properties.Group.isQuasigroup
d_isQuasigroup_556 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2944
d_isQuasigroup_556 ~v0 ~v1 v2 = du_isQuasigroup_556 v2
du_isQuasigroup_556 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2944
du_isQuasigroup_556 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsQuasigroup'46'constructor_106057
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
               (coe MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0)))))
      (coe du_'92''92''45'cong'8322'_516 (coe v0))
      (coe du_'47''47''45'cong'8322'_522 (coe v0))
      (coe du_'92''92''45'leftDivides_540 (coe v0))
      (coe du_'47''47''45'rightDivides_554 (coe v0))
-- Algebra.Properties.Group.quasigroup
d_quasigroup_558 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  MAlonzo.Code.Algebra.Bundles.T_Quasigroup_4246
d_quasigroup_558 ~v0 ~v1 v2 = du_quasigroup_558 v2
du_quasigroup_558 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  MAlonzo.Code.Algebra.Bundles.T_Quasigroup_4246
du_quasigroup_558 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Quasigroup'46'constructor_76277
      (MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Structures.du__'92''92'__1092
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
         (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Structures.du__'47''47'__1098
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
         (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0)))
      (coe du_isQuasigroup_556 (coe v0))
-- Algebra.Properties.Group._.x≈z//y
d_x'8776'z'47''47'y_562 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8776'z'47''47'y_562 ~v0 ~v1 v2 = du_x'8776'z'47''47'y_562 v2
du_x'8776'z'47''47'y_562 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8776'z'47''47'y_562 v0
  = coe
      MAlonzo.Code.Algebra.Properties.QQuasigroup.du_x'8776'z'47''47'y_300
      (coe du_quasigroup_558 (coe v0))
-- Algebra.Properties.Group._.y≈x\\z
d_y'8776'x'92''92'z_564 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_y'8776'x'92''92'z_564 ~v0 ~v1 v2 = du_y'8776'x'92''92'z_564 v2
du_y'8776'x'92''92'z_564 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_y'8776'x'92''92'z_564 v0
  = coe
      MAlonzo.Code.Algebra.Properties.QQuasigroup.du_y'8776'x'92''92'z_284
      (coe du_quasigroup_558 (coe v0))
-- Algebra.Properties.Group._.cancel
d_cancel_566 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cancel_566 ~v0 ~v1 v2 = du_cancel_566 v2
du_cancel_566 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cancel_566 v0
  = coe
      MAlonzo.Code.Algebra.Properties.QQuasigroup.du_cancel_276
      (coe du_quasigroup_558 (coe v0))
-- Algebra.Properties.Group._.cancelʳ
d_cancel'691'_568 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cancel'691'_568 ~v0 ~v1 v2 = du_cancel'691'_568 v2
du_cancel'691'_568 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_cancel'691'_568 v0
  = coe
      MAlonzo.Code.Algebra.Properties.QQuasigroup.du_cancel'691'_266
      (coe du_quasigroup_558 (coe v0))
-- Algebra.Properties.Group._.cancelˡ
d_cancel'737'_570 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cancel'737'_570 ~v0 ~v1 v2 = du_cancel'737'_570 v2
du_cancel'737'_570 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_cancel'737'_570 v0
  = coe
      MAlonzo.Code.Algebra.Properties.QQuasigroup.du_cancel'737'_256
      (coe du_quasigroup_558 (coe v0))
-- Algebra.Properties.Group.isLoop
d_isLoop_572 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3026
d_isLoop_572 ~v0 ~v1 v2 = du_isLoop_572 v2
du_isLoop_572 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3026
du_isLoop_572 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsLoop'46'constructor_111285
      (coe du_isQuasigroup_556 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Structures.d_identity_698
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
            (coe MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0))))
-- Algebra.Properties.Group.loop
d_loop_574 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  MAlonzo.Code.Algebra.Bundles.T_Loop_4346
d_loop_574 ~v0 ~v1 v2 = du_loop_574 v2
du_loop_574 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  MAlonzo.Code.Algebra.Bundles.T_Loop_4346
du_loop_574 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Loop'46'constructor_78267
      (MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Structures.du__'92''92'__1092
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
         (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Structures.du__'47''47'__1098
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
         (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0)))
      (MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v0))
      (coe du_isLoop_572 (coe v0))
-- Algebra.Properties.Group._.identity-unique
d_identity'45'unique_578 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_identity'45'unique_578 ~v0 ~v1 v2 = du_identity'45'unique_578 v2
du_identity'45'unique_578 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_identity'45'unique_578 v0
  = coe
      MAlonzo.Code.Algebra.Properties.Loop.du_identity'45'unique_326
      (coe du_loop_574 (coe v0))
-- Algebra.Properties.Group._.identityʳ-unique
d_identity'691''45'unique_580 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_identity'691''45'unique_580 ~v0 ~v1 v2
  = du_identity'691''45'unique_580 v2
du_identity'691''45'unique_580 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_identity'691''45'unique_580 v0
  = coe
      MAlonzo.Code.Algebra.Properties.Loop.du_identity'691''45'unique_316
      (coe du_loop_574 (coe v0))
-- Algebra.Properties.Group._.identityˡ-unique
d_identity'737''45'unique_582 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_identity'737''45'unique_582 ~v0 ~v1 v2
  = du_identity'737''45'unique_582 v2
du_identity'737''45'unique_582 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_identity'737''45'unique_582 v0
  = coe
      MAlonzo.Code.Algebra.Properties.Loop.du_identity'737''45'unique_304
      (coe du_loop_574 (coe v0))
-- Algebra.Properties.Group.inverseˡ-unique
d_inverse'737''45'unique_588 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'737''45'unique_588 ~v0 ~v1 v2 v3 v4 v5
  = du_inverse'737''45'unique_588 v2 v3 v4 v5
du_inverse'737''45'unique_588 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_inverse'737''45'unique_588 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
                  (coe MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0))))))
      v1
      (coe
         MAlonzo.Code.Algebra.Structures.du__'47''47'__1098
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
         (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
         (coe MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v0)) (coe v2))
      (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v2)
      (coe
         MAlonzo.Code.Algebra.Properties.QQuasigroup.du_x'8776'z'47''47'y_300
         (coe du_quasigroup_558 (coe v0)) (coe v1) (coe v2)
         (coe MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v0)) (coe v3))
      (let v4 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_identity'737'_726
            (MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v4))
            (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v2)))
-- Algebra.Properties.Group.inverseʳ-unique
d_inverse'691''45'unique_600 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'691''45'unique_600 ~v0 ~v1 v2 v3 v4 v5
  = du_inverse'691''45'unique_600 v2 v3 v4 v5
du_inverse'691''45'unique_600 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_inverse'691''45'unique_600 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
                  (coe MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0))))))
      v2
      (coe
         MAlonzo.Code.Algebra.Structures.du__'92''92'__1092
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
         (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
         (coe v1) (coe MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v0)))
      (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1)
      (coe
         MAlonzo.Code.Algebra.Properties.QQuasigroup.du_y'8776'x'92''92'z_284
         (coe du_quasigroup_558 (coe v0)) (coe v1) (coe v2)
         (coe MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v0)) (coe v3))
      (let v4 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_identity'691'_728
            (MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v4))
            (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1)))
-- Algebra.Properties.Group.ε⁻¹≈ε
d_ε'8315''185''8776'ε_608 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 -> AgdaAny
d_ε'8315''185''8776'ε_608 ~v0 ~v1 v2
  = du_ε'8315''185''8776'ε_608 v2
du_ε'8315''185''8776'ε_608 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 -> AgdaAny
du_ε'8315''185''8776'ε_608 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
                  (coe MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0))))))
      (MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0
         (MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v0)))
      (coe
         du_inverse'737''45'unique_588 (coe v0)
         (coe MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v0))
         (coe MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v0))
         (let v1 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_identity'737'_726
               (MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v1))
               (MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v0)))))
-- Algebra.Properties.Group.⁻¹-selfInverse
d_'8315''185''45'selfInverse_610 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'selfInverse_610 ~v0 ~v1 v2 v3 v4 v5
  = du_'8315''185''45'selfInverse_610 v2 v3 v4 v5
du_'8315''185''45'selfInverse_610 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8315''185''45'selfInverse_610 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
                  (coe MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0))))))
      v1 (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v2)
      (coe
         du_inverse'737''45'unique_588 (coe v0) (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v1 v2)
            (MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v0))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v4 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                         coe
                           (let v5
                                  = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v4) in
                            coe
                              (let v6
                                     = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v5) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.du_setoid_200
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                       (coe v6)))))))))
               (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v4 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                      coe
                        (let v5
                               = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v4) in
                         coe
                           (let v6
                                  = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v5) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_setoid_200
                                 (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v6))))))))
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v1 v2)
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v1
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1))
               (MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v0))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (let v4 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                            coe
                              (let v5
                                     = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v4) in
                               coe
                                 (let v6
                                        = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
                                            (coe v5) in
                                  coe
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.du_setoid_200
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                          (coe v6)))))))))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v1
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1))
                  (MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v0))
                  (MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v0))
                  (let v4
                         = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                             (coe
                                MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                (let v4 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                                 coe
                                   (let v5
                                          = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
                                              (coe v4) in
                                    coe
                                      (let v6
                                             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
                                                 (coe v5) in
                                       coe
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.du_setoid_200
                                            (coe
                                               MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                               (coe v6))))))) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                           (coe v4))
                        (coe MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v0))))
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_inverse'691'_1108
                     (MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0)) v1))
               (let v4 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                coe
                  (let v5
                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v4) in
                   coe
                     (let v6
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v5) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'737'_202
                           (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v6))
                           (coe v1)
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1)
                           (coe v2) (coe v3))))))))
-- Algebra.Properties.Group.⁻¹-involutive
d_'8315''185''45'involutive_618 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 -> AgdaAny -> AgdaAny
d_'8315''185''45'involutive_618 ~v0 ~v1 v2
  = du_'8315''185''45'involutive_618 v2
du_'8315''185''45'involutive_618 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 -> AgdaAny -> AgdaAny
du_'8315''185''45'involutive_618 v0
  = coe
      MAlonzo.Code.Algebra.Consequences.Setoid.du_selfInverse'8658'involutive_272
      (let v1 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
       coe
         (let v2
                = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v1) in
          coe
            (let v3
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v2) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_setoid_200
                  (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v3))))))
      (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
      (coe du_'8315''185''45'selfInverse_610 (coe v0))
-- Algebra.Properties.Group.x∙y⁻¹≈ε⇒x≈y
d_x'8729'y'8315''185''8776'ε'8658'x'8776'y_624 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8729'y'8315''185''8776'ε'8658'x'8776'y_624 ~v0 ~v1 v2 v3 v4 v5
  = du_x'8729'y'8315''185''8776'ε'8658'x'8776'y_624 v2 v3 v4 v5
du_x'8729'y'8315''185''8776'ε'8658'x'8776'y_624 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8729'y'8315''185''8776'ε'8658'x'8776'y_624 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v4 v5 v6 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
      v1 v2
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v4 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                   coe
                     (let v5
                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v4) in
                      coe
                        (let v6
                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v5) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_setoid_200
                              (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v6)))))))))
         v1
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v2))
         v2
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v4 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                      coe
                        (let v5
                               = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v4) in
                         coe
                           (let v6
                                  = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v5) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_setoid_200
                                 (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v6)))))))))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0
               (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v2))
            v2 v2
            (let v4
                   = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                       (coe
                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                          (let v4 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                           coe
                             (let v5
                                    = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v4) in
                              coe
                                (let v6
                                       = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
                                           (coe v5) in
                                 coe
                                   (coe
                                      MAlonzo.Code.Algebra.Structures.du_setoid_200
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                         (coe v6))))))) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                     (coe v4))
                  (coe v2)))
            (coe du_'8315''185''45'involutive_618 v0 v2))
         (coe
            du_inverse'737''45'unique_588 (coe v0) (coe v1)
            (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v2)
            (coe v3)))
-- Algebra.Properties.Group.x≈y⇒x∙y⁻¹≈ε
d_x'8776'y'8658'x'8729'y'8315''185''8776'ε_636 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8776'y'8658'x'8729'y'8315''185''8776'ε_636 ~v0 ~v1 v2 v3 v4 v5
  = du_x'8776'y'8658'x'8729'y'8315''185''8776'ε_636 v2 v3 v4 v5
du_x'8776'y'8658'x'8729'y'8315''185''8776'ε_636 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8776'y'8658'x'8729'y'8315''185''8776'ε_636 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v4 v5 v6 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v1
         (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v2))
      (MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v4 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                   coe
                     (let v5
                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v4) in
                      coe
                        (let v6
                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v5) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_setoid_200
                              (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v6)))))))))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v1
            (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v2))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v2
            (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v2))
         (MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v4 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                      coe
                        (let v5
                               = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v4) in
                         coe
                           (let v6
                                  = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v5) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_setoid_200
                                 (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v6)))))))))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v2
               (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v2))
            (MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v0))
            (MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v0))
            (let v4
                   = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                       (coe
                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                          (let v4 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                           coe
                             (let v5
                                    = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v4) in
                              coe
                                (let v6
                                       = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
                                           (coe v5) in
                                 coe
                                   (coe
                                      MAlonzo.Code.Algebra.Structures.du_setoid_200
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                         (coe v6))))))) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                     (coe v4))
                  (coe MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v0))))
            (coe
               MAlonzo.Code.Algebra.Structures.du_inverse'691'_1108
               (MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0)) v2))
         (let v4 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
          coe
            (let v5
                   = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v4) in
             coe
               (let v6
                      = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v5) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'691'_206
                     (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v6))
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v2)
                     (coe v1) (coe v2) (coe v3))))))
-- Algebra.Properties.Group.⁻¹-injective
d_'8315''185''45'injective_644 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'injective_644 ~v0 ~v1 v2 v3 v4
  = du_'8315''185''45'injective_644 v2 v3 v4
du_'8315''185''45'injective_644 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8315''185''45'injective_644 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Consequences.Setoid.du_selfInverse'8658'injective_288
      (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
       coe
         (let v4
                = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3) in
          coe
            (let v5
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v4) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_setoid_200
                  (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))))))
      (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
      (coe du_'8315''185''45'selfInverse_610 (coe v0)) (coe v1) (coe v2)
-- Algebra.Properties.Group.⁻¹-anti-homo-∙
d_'8315''185''45'anti'45'homo'45''8729'_650 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'anti'45'homo'45''8729'_650 ~v0 ~v1 v2 v3 v4
  = du_'8315''185''45'anti'45'homo'45''8729'_650 v2 v3 v4
du_'8315''185''45'anti'45'homo'45''8729'_650 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8315''185''45'anti'45'homo'45''8729'_650 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Properties.QQuasigroup.du_cancel'737'_256
      (coe du_quasigroup_558 (coe v0))
      (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v1 v2)
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v1 v2))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v2)
         (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v5)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v1 v2)
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v1 v2)))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v1 v2)
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
               (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v2)
               (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1)))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                      coe
                        (let v4
                               = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3) in
                         coe
                           (let v5
                                  = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v4) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_setoid_200
                                 (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5)))))))))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v1 v2)
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v1 v2)))
            (MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v0))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v1 v2)
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v2)
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1)))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                         coe
                           (let v4
                                  = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3) in
                            coe
                              (let v5
                                     = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v4) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.du_setoid_200
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                       (coe v5)))))))))
               (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                      coe
                        (let v4
                               = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3) in
                         coe
                           (let v5
                                  = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v4) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_setoid_200
                                 (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))))))))
               (MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v0))
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v1
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1))
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v1 v2)
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v2)
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1)))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                            coe
                              (let v4
                                     = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3) in
                               coe
                                 (let v5
                                        = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
                                            (coe v4) in
                                  coe
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.du_setoid_200
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                          (coe v5)))))))))
                  (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                         coe
                           (let v4
                                  = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3) in
                            coe
                              (let v5
                                     = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v4) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.du_setoid_200
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))))))))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v1
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v1 v2)
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v2))
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v1 v2)
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v2)
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1)))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                              (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                               coe
                                 (let v4
                                        = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
                                            (coe v3) in
                                  coe
                                    (let v5
                                           = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
                                               (coe v4) in
                                     coe
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.du_setoid_200
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                             (coe v5)))))))))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v1 v2)
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v2))
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v1 v2)
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v2)
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1)))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v1 v2)
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v2)
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1)))
                     (let v3
                            = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                (coe
                                   MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                   (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                                    coe
                                      (let v4
                                             = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
                                                 (coe v3) in
                                       coe
                                         (let v5
                                                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
                                                    (coe v4) in
                                          coe
                                            (coe
                                               MAlonzo.Code.Algebra.Structures.du_setoid_200
                                               (coe
                                                  MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                                  (coe v5))))))) in
                      coe
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                              (coe v3))
                           (coe
                              MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
                              (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v1 v2)
                              (coe
                                 MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
                                 (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v2)
                                 (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1)))))
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_assoc_482
                        (MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
                              (coe MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0))))
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v1 v2)
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v2)
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1)))
                  (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                   coe
                     (let v4
                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3) in
                      coe
                        (let v5
                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v4) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'691'_206
                              (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))
                              (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1)
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du__'47''47'__1098
                                 (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
                                 (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
                                 (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v1 v2)
                                 (coe v2))
                              (coe v1)
                              (coe
                                 du_'47''47''45'rightDivides'691'_548 (coe v0) (coe v2)
                                 (coe v1)))))))
               (coe
                  MAlonzo.Code.Algebra.Structures.du_inverse'691'_1108
                  (MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0)) v1))
            (coe
               MAlonzo.Code.Algebra.Structures.du_inverse'691'_1108
               (MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0))
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v1 v2))))
-- Algebra.Properties.Group.⁻¹-anti-homo-//
d_'8315''185''45'anti'45'homo'45''47''47'_660 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'anti'45'homo'45''47''47'_660 ~v0 ~v1 v2 v3 v4
  = du_'8315''185''45'anti'45'homo'45''47''47'_660 v2 v3 v4
du_'8315''185''45'anti'45'homo'45''47''47'_660 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8315''185''45'anti'45'homo'45''47''47'_660 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v3 v4 v5 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v5)
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0
         (coe
            MAlonzo.Code.Algebra.Structures.du__'47''47'__1098
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
            (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
            (coe v1) (coe v2)))
      (coe
         MAlonzo.Code.Algebra.Structures.du__'47''47'__1098
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
         (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
         (coe v2) (coe v1))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                   coe
                     (let v4
                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3) in
                      coe
                        (let v5
                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v4) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_setoid_200
                              (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5)))))))))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v1
               (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v2)))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0
               (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v2))
            (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1))
         (coe
            MAlonzo.Code.Algebra.Structures.du__'47''47'__1098
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
            (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
            (coe v2) (coe v1))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                      coe
                        (let v4
                               = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3) in
                         coe
                           (let v5
                                  = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v4) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_setoid_200
                                 (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5)))))))))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v2))
               (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v2
               (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1))
            (coe
               MAlonzo.Code.Algebra.Structures.du__'47''47'__1098
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
               (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
               (coe v2) (coe v1))
            (let v3
                   = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                       (coe
                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                          (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                           coe
                             (let v4
                                    = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3) in
                              coe
                                (let v5
                                       = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
                                           (coe v4) in
                                 coe
                                   (coe
                                      MAlonzo.Code.Algebra.Structures.du_setoid_200
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                         (coe v5))))))) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                     (coe v3))
                  (coe
                     MAlonzo.Code.Algebra.Structures.du__'47''47'__1098
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
                     (coe v2) (coe v1))))
            (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
             coe
               (let v4
                      = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3) in
                coe
                  (let v5
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'691'_206
                        (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1)
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v2))
                        (coe v2) (coe du_'8315''185''45'involutive_618 v0 v2))))))
         (coe
            du_'8315''185''45'anti'45'homo'45''8729'_650 (coe v0) (coe v1)
            (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v2)))
-- Algebra.Properties.Group.⁻¹-anti-homo-\\
d_'8315''185''45'anti'45'homo'45''92''92'_670 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'anti'45'homo'45''92''92'_670 ~v0 ~v1 v2 v3 v4
  = du_'8315''185''45'anti'45'homo'45''92''92'_670 v2 v3 v4
du_'8315''185''45'anti'45'homo'45''92''92'_670 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8315''185''45'anti'45'homo'45''92''92'_670 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v3 v4 v5 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v5)
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0
         (coe
            MAlonzo.Code.Algebra.Structures.du__'92''92'__1092
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
            (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
            (coe v1) (coe v2)))
      (coe
         MAlonzo.Code.Algebra.Structures.du__'92''92'__1092
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
         (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
         (coe v2) (coe v1))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                   coe
                     (let v4
                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3) in
                      coe
                        (let v5
                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v4) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_setoid_200
                              (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5)))))))))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
               (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1) v2))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v2)
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0
               (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1)))
         (coe
            MAlonzo.Code.Algebra.Structures.du__'92''92'__1092
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
            (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
            (coe v2) (coe v1))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                      coe
                        (let v4
                               = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3) in
                         coe
                           (let v5
                                  = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v4) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_setoid_200
                                 (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5)))))))))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
               (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v2)
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1)))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
               (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v2) v1)
            (coe
               MAlonzo.Code.Algebra.Structures.du__'92''92'__1092
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
               (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
               (coe v2) (coe v1))
            (let v3
                   = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                       (coe
                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                          (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                           coe
                             (let v4
                                    = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3) in
                              coe
                                (let v5
                                       = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
                                           (coe v4) in
                                 coe
                                   (coe
                                      MAlonzo.Code.Algebra.Structures.du_setoid_200
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                         (coe v5))))))) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                     (coe v3))
                  (coe
                     MAlonzo.Code.Algebra.Structures.du__'92''92'__1092
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
                     (coe v2) (coe v1))))
            (let v3 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
             coe
               (let v4
                      = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3) in
                coe
                  (let v5
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'737'_202
                        (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v2)
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1))
                        (coe v1) (coe du_'8315''185''45'involutive_618 v0 v1))))))
         (coe
            du_'8315''185''45'anti'45'homo'45''8729'_650 (coe v0)
            (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v1)
            (coe v2)))
-- Algebra.Properties.Group.\\≗flip-//⇒comm
d_'92''92''8791'flip'45''47''47''8658'comm_680 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''8791'flip'45''47''47''8658'comm_680 ~v0 ~v1 v2 v3 v4 v5
  = du_'92''92''8791'flip'45''47''47''8658'comm_680 v2 v3 v4 v5
du_'92''92''8791'flip'45''47''47''8658'comm_680 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_'92''92''8791'flip'45''47''47''8658'comm_680 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v4 v5 v6 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
      (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v2 v3)
      (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v3 v2)
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v4 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                   coe
                     (let v5
                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v4) in
                      coe
                        (let v6
                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v5) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_setoid_200
                              (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v6)))))))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
               (let v4 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                coe
                  (let v5
                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v4) in
                   coe
                     (let v6
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v5) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_setoid_200
                           (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v6))))))))
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v2 v3)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v2
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
               (coe
                  MAlonzo.Code.Algebra.Structures.du__'47''47'__1098
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
                  (coe v3) (coe v2))
               v2))
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v3 v2)
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v4 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                      coe
                        (let v5
                               = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v4) in
                         coe
                           (let v6
                                  = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v5) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_setoid_200
                                 (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v6)))))))))
            (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v4 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                   coe
                     (let v5
                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v4) in
                      coe
                        (let v6
                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v5) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_setoid_200
                              (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v6))))))))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v2
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
                  (coe
                     MAlonzo.Code.Algebra.Structures.du__'47''47'__1098
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
                     (coe v3) (coe v2))
                  v2))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v2
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
                  (coe
                     MAlonzo.Code.Algebra.Structures.du__'92''92'__1092
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
                     (coe v2) (coe v3))
                  v2))
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v3 v2)
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v4 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                         coe
                           (let v5
                                  = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v4) in
                            coe
                              (let v6
                                     = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v5) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.du_setoid_200
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                       (coe v6)))))))))
               (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v4 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                      coe
                        (let v5
                               = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v4) in
                         coe
                           (let v6
                                  = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v5) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_setoid_200
                                 (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v6))))))))
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v2
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
                     (coe
                        MAlonzo.Code.Algebra.Structures.du__'92''92'__1092
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
                        (coe v2) (coe v3))
                     v2))
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v2
                     (coe
                        MAlonzo.Code.Algebra.Structures.du__'92''92'__1092
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
                        (coe v2) (coe v3)))
                  v2)
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v3 v2)
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (let v4 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                            coe
                              (let v5
                                     = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v4) in
                               coe
                                 (let v6
                                        = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
                                            (coe v5) in
                                  coe
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.du_setoid_200
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                          (coe v6)))))))))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v2
                        (coe
                           MAlonzo.Code.Algebra.Structures.du__'92''92'__1092
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
                           (coe v2) (coe v3)))
                     v2)
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v3 v2)
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v3 v2)
                  (let v4
                         = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                             (coe
                                MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                (let v4 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                                 coe
                                   (let v5
                                          = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
                                              (coe v4) in
                                    coe
                                      (let v6
                                             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
                                                 (coe v5) in
                                       coe
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.du_setoid_200
                                            (coe
                                               MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                               (coe v6))))))) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                           (coe v4))
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v3 v2)))
                  (let v4 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                   coe
                     (let v5
                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v4) in
                      coe
                        (let v6
                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v5) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'691'_206
                              (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v6))
                              (coe v2)
                              (coe
                                 MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v2
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.du__'92''92'__1092
                                    (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
                                    (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
                                    (coe v2) (coe v3)))
                              (coe v3)
                              (coe
                                 du_'92''92''45'leftDivides'737'_528 (coe v0) (coe v2)
                                 (coe v3)))))))
               (coe
                  MAlonzo.Code.Algebra.Structures.d_assoc_482
                  (MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
                        (coe MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0))))
                  v2
                  (coe
                     MAlonzo.Code.Algebra.Structures.du__'92''92'__1092
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
                     (coe v2) (coe v3))
                  v2))
            (let v4 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'737'_202
                        (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v6))
                        (coe v2)
                        (coe
                           MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                           (\ v7 -> coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v7 v2)
                           (\ v7 v8 -> v7)
                           (coe
                              MAlonzo.Code.Algebra.Structures.du__'92''92'__1092
                              (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
                              (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
                              (coe v2) (coe v3))
                           (coe
                              MAlonzo.Code.Algebra.Structures.du__'47''47'__1098
                              (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
                              (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
                              (coe v3) (coe v2)))
                        (coe
                           MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                           (\ v7 v8 -> v8)
                           (\ v7 -> coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v7 v2)
                           (coe
                              MAlonzo.Code.Algebra.Structures.du__'92''92'__1092
                              (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
                              (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
                              (coe v2) (coe v3))
                           (coe
                              MAlonzo.Code.Algebra.Structures.du__'47''47'__1098
                              (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
                              (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
                              (coe v3) (coe v2)))
                        (let v7 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                         coe
                           (let v8
                                  = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v7) in
                            coe
                              (let v9
                                     = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v8) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'691'_206
                                    (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v9))
                                    (coe v2)
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.du__'92''92'__1092
                                       (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
                                       (coe
                                          MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
                                       (coe v2) (coe v3))
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.du__'47''47'__1098
                                       (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
                                       (coe
                                          MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
                                       (coe v3) (coe v2))
                                    (coe v1 v2 v3))))))))))
         (let v4 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
          coe
            (let v5
                   = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v4) in
             coe
               (let v6
                      = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v5) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'737'_202
                     (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v6))
                     (coe v2)
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
                        (coe
                           MAlonzo.Code.Algebra.Structures.du__'47''47'__1098
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
                           (coe v3) (coe v2))
                        v2)
                     (coe v3)
                     (coe
                        du_'47''47''45'rightDivides'737'_542 (coe v0) (coe v2)
                        (coe v3)))))))
-- Algebra.Properties.Group.comm⇒\\≗flip-//
d_comm'8658''92''92''8791'flip'45''47''47'_692 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_comm'8658''92''92''8791'flip'45''47''47'_692 ~v0 ~v1 v2 v3 v4 v5
  = du_comm'8658''92''92''8791'flip'45''47''47'_692 v2 v3 v4 v5
du_comm'8658''92''92''8791'flip'45''47''47'_692 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_comm'8658''92''92''8791'flip'45''47''47'_692 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v4 v5 v6 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
      (coe
         MAlonzo.Code.Algebra.Structures.du__'92''92'__1092
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
         (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
         (coe v2) (coe v3))
      (coe
         MAlonzo.Code.Algebra.Structures.du__'47''47'__1098
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
         (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
         (coe v3) (coe v2))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v4 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                   coe
                     (let v5
                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v4) in
                      coe
                        (let v6
                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v5) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_setoid_200
                              (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v6)))))))))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v2) v3)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0 v3
            (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v2))
         (coe
            MAlonzo.Code.Algebra.Structures.du__'47''47'__1098
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
            (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
            (coe v3) (coe v2))
         (let v4
                = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                    (coe
                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                       (let v4 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0) in
                        coe
                          (let v5
                                 = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v4) in
                           coe
                             (let v6
                                    = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v5) in
                              coe
                                (coe
                                   MAlonzo.Code.Algebra.Structures.du_setoid_200
                                   (coe
                                      MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                      (coe v6))))))) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                  (coe v4))
               (coe
                  MAlonzo.Code.Algebra.Structures.du__'47''47'__1098
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v0))
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0))
                  (coe v3) (coe v2))))
         (coe
            v1 (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v2)
            v3))
