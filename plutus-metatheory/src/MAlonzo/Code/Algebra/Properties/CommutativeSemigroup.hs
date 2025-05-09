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

module MAlonzo.Code.Algebra.Properties.CommutativeSemigroup where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Algebra.Bundles qualified
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

-- Algebra.Properties.CommutativeSemigroup._.Interchangable
d_Interchangable_108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Interchangable_108 = erased
-- Algebra.Properties.CommutativeSemigroup._.LeftSemimedial
d_LeftSemimedial_138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftSemimedial_138 = erased
-- Algebra.Properties.CommutativeSemigroup._.RightSemimedial
d_RightSemimedial_168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightSemimedial_168 = erased
-- Algebra.Properties.CommutativeSemigroup._.Semimedial
d_Semimedial_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Semimedial_176 = erased
-- Algebra.Properties.CommutativeSemigroup._.alternative
d_alternative_234 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_alternative_234 ~v0 ~v1 v2 = du_alternative_234 v2
du_alternative_234 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_alternative_234 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Structures.d_assoc_482
              (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                 (coe
                    MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                    (coe v0)))
              v1 v1 v2))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_sym_36
              (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                 (coe
                    MAlonzo.Code.Algebra.Structures.d_isMagma_480
                    (coe
                       MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                       (coe
                          MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                 (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2) v2)
              (coe
                 MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
                 (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v2))
              (coe
                 MAlonzo.Code.Algebra.Structures.d_assoc_482
                 (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                    (coe
                       MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                       (coe v0)))
                 v1 v2 v2)))
-- Algebra.Properties.CommutativeSemigroup._.alternativeʳ
d_alternative'691'_236 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_alternative'691'_236 ~v0 ~v1 v2 v3 v4
  = du_alternative'691'_236 v2 v3 v4
du_alternative'691'_236 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_alternative'691'_236 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
               (coe
                  MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                  (coe v0)))))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2) v2)
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v2))
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_482
         (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
            (coe
               MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
               (coe v0)))
         v1 v2 v2)
-- Algebra.Properties.CommutativeSemigroup._.alternativeˡ
d_alternative'737'_238 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_alternative'737'_238 ~v0 ~v1 v2 v3 v4
  = du_alternative'737'_238 v2 v3 v4
du_alternative'737'_238 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_alternative'737'_238 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Structures.d_assoc_482
      (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
         (coe
            MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
            (coe v0)))
      v1 v1 v2
-- Algebra.Properties.CommutativeSemigroup._.flexible
d_flexible_240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_flexible_240 ~v0 ~v1 v2 v3 v4 = du_flexible_240 v2 v3 v4
du_flexible_240 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_flexible_240 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Structures.d_assoc_482
      (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
         (coe
            MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
            (coe v0)))
      v1 v2 v1
-- Algebra.Properties.CommutativeSemigroup._.x∙yz≈xy∙z
d_x'8729'yz'8776'xy'8729'z_242 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8729'yz'8776'xy'8729'z_242 ~v0 ~v1 v2 v3 v4 v5
  = du_x'8729'yz'8776'xy'8729'z_242 v2 v3 v4 v5
du_x'8729'yz'8776'xy'8729'z_242 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8729'yz'8776'xy'8729'z_242 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
               (coe
                  MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                  (coe v0)))))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2) v3)
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3))
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_482
         (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
            (coe
               MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
               (coe v0)))
         v1 v2 v3)
-- Algebra.Properties.CommutativeSemigroup.interchange
d_interchange_244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_interchange_244 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_interchange_244 v2 v3 v4 v5 v6
du_interchange_244 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_interchange_244 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v5 v6 v7 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v7)
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2)
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v4))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3)
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v4))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v5
                         = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                             (coe v0) in
                   coe
                     (let v6
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v5) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_setoid_200
                           (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v6))))))))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2)
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v4))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v4)))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3)
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v4))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v5
                            = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                (coe v0) in
                      coe
                        (let v6
                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v5) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_setoid_200
                              (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v6))))))))
            (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v5
                         = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                             (coe v0) in
                   coe
                     (let v6
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v5) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_setoid_200
                           (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v6)))))))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v4)))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3) v4))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3)
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v4))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v5
                               = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                   (coe v0) in
                         coe
                           (let v6
                                  = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v5) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_setoid_200
                                 (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v6))))))))
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3) v4))
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v2) v4))
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3)
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v4))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (let v5
                                  = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                      (coe v0) in
                            coe
                              (let v6
                                     = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v5) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.du_setoid_200
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v6))))))))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v2) v4))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v4)))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3)
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v4))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                              (let v5
                                     = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                         (coe v0) in
                               coe
                                 (let v6
                                        = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                                            (coe v5) in
                                  coe
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.du_setoid_200
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                          (coe v6))))))))
                     (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (let v5
                                  = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                      (coe v0) in
                            coe
                              (let v6
                                     = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v5) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.du_setoid_200
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v6)))))))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v4)))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3)
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v4))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3)
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v4))
                     (let v5
                            = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                (coe
                                   MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                   (let v5
                                          = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                              (coe v0) in
                                    coe
                                      (let v6
                                             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                                                 (coe v5) in
                                       coe
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.du_setoid_200
                                            (coe
                                               MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                               (coe v6)))))) in
                      coe
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                              (coe v5))
                           (coe
                              MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                              (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3)
                              (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v4))))
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_assoc_482
                        (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                           (coe
                              MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                              (coe v0)))
                        v1 v3 (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v4)))
                  (let v5
                         = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                             (coe v0) in
                   coe
                     (let v6
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v5) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'737'_202
                           (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v6))
                           (coe v1)
                           (coe
                              MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                              (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v2) v4)
                           (coe
                              MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3
                              (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v4))
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_assoc_482
                              (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                                 (coe
                                    MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                    (coe v0)))
                              v3 v2 v4)))))
               (let v5
                      = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                          (coe v0) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'737'_202
                        (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v6))
                        (coe v1)
                        (coe
                           MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                           (\ v7 -> coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v7 v4)
                           (\ v7 v8 -> v7)
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3)
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v2))
                        (coe
                           MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                           (\ v7 v8 -> v8)
                           (\ v7 -> coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v7 v4)
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3)
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v2))
                        (let v7
                               = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                   (coe v0) in
                         coe
                           (let v8
                                  = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v7) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'691'_206
                                 (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v8))
                                 (coe v4) (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3)
                                 (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v2)
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.d_comm_558
                                    (MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                       (coe v0))
                                    v2 v3))))))))
            (let v5
                   = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                       (coe v0) in
             coe
               (let v6
                      = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v5) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'737'_202
                     (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v6))
                     (coe v1)
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3) v4)
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v4))
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_assoc_482
                        (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                           (coe
                              MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                              (coe v0)))
                        v2 v3 v4)))))
         (coe
            MAlonzo.Code.Algebra.Structures.d_assoc_482
            (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
               (coe
                  MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                  (coe v0)))
            v1 v2 (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v4)))
-- Algebra.Properties.CommutativeSemigroup.x∙yz≈y∙xz
d_x'8729'yz'8776'y'8729'xz_260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8729'yz'8776'y'8729'xz_260 ~v0 ~v1 v2 v3 v4 v5
  = du_x'8729'yz'8776'y'8729'xz_260 v2 v3 v4 v5
du_x'8729'yz'8776'y'8729'xz_260 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8729'yz'8776'y'8729'xz_260 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v4 v5 v6 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v4
                         = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                             (coe v0) in
                   coe
                     (let v5
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v4) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_setoid_200
                           (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))))))))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2) v3)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v4
                            = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                (coe v0) in
                      coe
                        (let v5
                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v4) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_setoid_200
                              (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))))))))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2) v3)
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1) v3)
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v4
                               = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                   (coe v0) in
                         coe
                           (let v5
                                  = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v4) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_setoid_200
                                 (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))))))))
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1) v3)
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3))
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3))
               (let v4
                      = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                          (coe
                             MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                             (let v4
                                    = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                        (coe v0) in
                              coe
                                (let v5
                                       = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                                           (coe v4) in
                                 coe
                                   (coe
                                      MAlonzo.Code.Algebra.Structures.du_setoid_200
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                         (coe v5)))))) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                        (coe v4))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3))))
               (coe
                  MAlonzo.Code.Algebra.Structures.d_assoc_482
                  (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                        (coe v0)))
                  v2 v1 v3))
            (let v4
                   = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                       (coe v0) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'691'_206
                     (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))
                     (coe v3) (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1)
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_comm_558
                        (MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                           (coe v0))
                        v1 v2)))))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMagma_480
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                        (coe v0)))))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2) v3)
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3))
            (coe
               MAlonzo.Code.Algebra.Structures.d_assoc_482
               (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                     (coe v0)))
               v1 v2 v3)))
-- Algebra.Properties.CommutativeSemigroup.x∙yz≈z∙yx
d_x'8729'yz'8776'z'8729'yx_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8729'yz'8776'z'8729'yx_274 ~v0 ~v1 v2 v3 v4 v5
  = du_x'8729'yz'8776'z'8729'yx_274 v2 v3 v4 v5
du_x'8729'yz'8776'z'8729'yx_274 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8729'yz'8776'z'8729'yx_274 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v4 v5 v6 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v4
                         = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                             (coe v0) in
                   coe
                     (let v5
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v4) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_setoid_200
                           (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))))))))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v2))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v4
                            = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                (coe v0) in
                      coe
                        (let v5
                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v4) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_setoid_200
                              (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))))))))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v2))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v4
                               = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                   (coe v0) in
                         coe
                           (let v5
                                  = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v4) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_setoid_200
                                 (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))))))))
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2))
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1))
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1))
               (let v4
                      = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                          (coe
                             MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                             (let v4
                                    = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                        (coe v0) in
                              coe
                                (let v5
                                       = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                                           (coe v4) in
                                 coe
                                   (coe
                                      MAlonzo.Code.Algebra.Structures.du_setoid_200
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                         (coe v5)))))) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                        (coe v4))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1))))
               (let v4
                      = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                          (coe v0) in
                coe
                  (let v5
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'737'_202
                        (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))
                        (coe v3) (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2)
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1)
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_comm_558
                           (MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                              (coe v0))
                           v1 v2)))))
            (coe
               du_x'8729'yz'8776'y'8729'xz_260 (coe v0) (coe v1) (coe v3)
               (coe v2)))
         (let v4
                = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                    (coe v0) in
          coe
            (let v5
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v4) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'737'_202
                  (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))
                  (coe v1) (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3)
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v2)
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_comm_558
                     (MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                        (coe v0))
                     v2 v3)))))
-- Algebra.Properties.CommutativeSemigroup.x∙yz≈x∙zy
d_x'8729'yz'8776'x'8729'zy_288 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8729'yz'8776'x'8729'zy_288 ~v0 ~v1 v2 v3 v4 v5
  = du_x'8729'yz'8776'x'8729'zy_288 v2 v3 v4 v5
du_x'8729'yz'8776'x'8729'zy_288 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8729'yz'8776'x'8729'zy_288 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
              (coe v0) in
    coe
      (let v5
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v4) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'737'_202
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))
            (coe v1) (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3)
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v2)
            (coe
               MAlonzo.Code.Algebra.Structures.d_comm_558
               (MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                  (coe v0))
               v2 v3)))
-- Algebra.Properties.CommutativeSemigroup.x∙yz≈y∙zx
d_x'8729'yz'8776'y'8729'zx_300 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8729'yz'8776'y'8729'zx_300 ~v0 ~v1 v2 v3 v4 v5
  = du_x'8729'yz'8776'y'8729'zx_300 v2 v3 v4 v5
du_x'8729'yz'8776'y'8729'zx_300 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8729'yz'8776'y'8729'zx_300 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v4 v5 v6 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v4
                         = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                             (coe v0) in
                   coe
                     (let v5
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v4) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_setoid_200
                           (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))))))))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3) v1)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v4
                            = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                (coe v0) in
                      coe
                        (let v5
                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v4) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_setoid_200
                              (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))))))))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3) v1)
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1))
            (let v4
                   = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                       (coe
                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                          (let v4
                                 = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                     (coe v0) in
                           coe
                             (let v5
                                    = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v4) in
                              coe
                                (coe
                                   MAlonzo.Code.Algebra.Structures.du_setoid_200
                                   (coe
                                      MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5)))))) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                     (coe v4))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1))))
            (coe
               MAlonzo.Code.Algebra.Structures.d_assoc_482
               (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                     (coe v0)))
               v2 v3 v1))
         (coe
            MAlonzo.Code.Algebra.Structures.d_comm_558
            (MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
               (coe v0))
            v1 (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3)))
-- Algebra.Properties.CommutativeSemigroup.x∙yz≈z∙xy
d_x'8729'yz'8776'z'8729'xy_314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8729'yz'8776'z'8729'xy_314 ~v0 ~v1 v2 v3 v4 v5
  = du_x'8729'yz'8776'z'8729'xy_314 v2 v3 v4 v5
du_x'8729'yz'8776'z'8729'xy_314 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8729'yz'8776'z'8729'xy_314 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v4 v5 v6 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v4
                         = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                             (coe v0) in
                   coe
                     (let v5
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v4) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_setoid_200
                           (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))))))))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2) v3)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v4
                            = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                (coe v0) in
                      coe
                        (let v5
                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v4) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_setoid_200
                              (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))))))))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2) v3)
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2))
            (let v4
                   = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                       (coe
                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                          (let v4
                                 = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                     (coe v0) in
                           coe
                             (let v5
                                    = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v4) in
                              coe
                                (coe
                                   MAlonzo.Code.Algebra.Structures.du_setoid_200
                                   (coe
                                      MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5)))))) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                     (coe v4))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2))))
            (coe
               MAlonzo.Code.Algebra.Structures.d_comm_558
               (MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                  (coe v0))
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2) v3))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMagma_480
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                        (coe v0)))))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2) v3)
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3))
            (coe
               MAlonzo.Code.Algebra.Structures.d_assoc_482
               (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                     (coe v0)))
               v1 v2 v3)))
-- Algebra.Properties.CommutativeSemigroup.x∙yz≈yx∙z
d_x'8729'yz'8776'yx'8729'z_328 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8729'yz'8776'yx'8729'z_328 ~v0 ~v1 v2 v3 v4 v5
  = du_x'8729'yz'8776'yx'8729'z_328 v2 v3 v4 v5
du_x'8729'yz'8776'yx'8729'z_328 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8729'yz'8776'yx'8729'z_328 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
               (coe
                  MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                  (coe v0)))))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1) v3)
      (coe
         du_x'8729'yz'8776'y'8729'xz_260 (coe v0) (coe v1) (coe v2)
         (coe v3))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_36
         (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_480
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                     (coe v0)))))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1) v3)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3))
         (coe
            MAlonzo.Code.Algebra.Structures.d_assoc_482
            (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
               (coe
                  MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                  (coe v0)))
            v2 v1 v3))
-- Algebra.Properties.CommutativeSemigroup.x∙yz≈zy∙x
d_x'8729'yz'8776'zy'8729'x_342 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8729'yz'8776'zy'8729'x_342 ~v0 ~v1 v2 v3 v4 v5
  = du_x'8729'yz'8776'zy'8729'x_342 v2 v3 v4 v5
du_x'8729'yz'8776'zy'8729'x_342 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8729'yz'8776'zy'8729'x_342 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
               (coe
                  MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                  (coe v0)))))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v2) v1)
      (coe
         du_x'8729'yz'8776'z'8729'yx_274 (coe v0) (coe v1) (coe v2)
         (coe v3))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_36
         (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_480
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                     (coe v0)))))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v2) v1)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1))
         (coe
            MAlonzo.Code.Algebra.Structures.d_assoc_482
            (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
               (coe
                  MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                  (coe v0)))
            v3 v2 v1))
-- Algebra.Properties.CommutativeSemigroup.x∙yz≈xz∙y
d_x'8729'yz'8776'xz'8729'y_356 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8729'yz'8776'xz'8729'y_356 ~v0 ~v1 v2 v3 v4 v5
  = du_x'8729'yz'8776'xz'8729'y_356 v2 v3 v4 v5
du_x'8729'yz'8776'xz'8729'y_356 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8729'yz'8776'xz'8729'y_356 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
               (coe
                  MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                  (coe v0)))))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v2))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3) v2)
      (coe
         du_x'8729'yz'8776'x'8729'zy_288 (coe v0) (coe v1) (coe v2)
         (coe v3))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_36
         (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_480
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                     (coe v0)))))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3) v2)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v2))
         (coe
            MAlonzo.Code.Algebra.Structures.d_assoc_482
            (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
               (coe
                  MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                  (coe v0)))
            v1 v3 v2))
-- Algebra.Properties.CommutativeSemigroup.x∙yz≈yz∙x
d_x'8729'yz'8776'yz'8729'x_370 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8729'yz'8776'yz'8729'x_370 ~v0 ~v1 v2 v3 v4 v5
  = du_x'8729'yz'8776'yz'8729'x_370 v2 v3 v4 v5
du_x'8729'yz'8776'yz'8729'x_370 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8729'yz'8776'yz'8729'x_370 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
               (coe
                  MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                  (coe v0)))))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3) v1)
      (coe
         du_x'8729'yz'8776'y'8729'zx_300 (coe v0) (coe v1) (coe v2)
         (coe v3))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_36
         (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_480
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                     (coe v0)))))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3) v1)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1))
         (coe
            MAlonzo.Code.Algebra.Structures.d_assoc_482
            (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
               (coe
                  MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                  (coe v0)))
            v2 v3 v1))
-- Algebra.Properties.CommutativeSemigroup.x∙yz≈zx∙y
d_x'8729'yz'8776'zx'8729'y_384 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8729'yz'8776'zx'8729'y_384 ~v0 ~v1 v2 v3 v4 v5
  = du_x'8729'yz'8776'zx'8729'y_384 v2 v3 v4 v5
du_x'8729'yz'8776'zx'8729'y_384 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8729'yz'8776'zx'8729'y_384 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
               (coe
                  MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                  (coe v0)))))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1) v2)
      (coe
         du_x'8729'yz'8776'z'8729'xy_314 (coe v0) (coe v1) (coe v2)
         (coe v3))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_36
         (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_480
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                     (coe v0)))))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1) v2)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2))
         (coe
            MAlonzo.Code.Algebra.Structures.d_assoc_482
            (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
               (coe
                  MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                  (coe v0)))
            v3 v1 v2))
-- Algebra.Properties.CommutativeSemigroup.xy∙z≈y∙xz
d_xy'8729'z'8776'y'8729'xz_398 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_xy'8729'z'8776'y'8729'xz_398 ~v0 ~v1 v2 v3 v4 v5
  = du_xy'8729'z'8776'y'8729'xz_398 v2 v3 v4 v5
du_xy'8729'z'8776'y'8729'xz_398 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_xy'8729'z'8776'y'8729'xz_398 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
               (coe
                  MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                  (coe v0)))))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2) v3)
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3))
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_482
         (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
            (coe
               MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
               (coe v0)))
         v1 v2 v3)
      (coe
         du_x'8729'yz'8776'y'8729'xz_260 (coe v0) (coe v1) (coe v2)
         (coe v3))
-- Algebra.Properties.CommutativeSemigroup.xy∙z≈z∙yx
d_xy'8729'z'8776'z'8729'yx_412 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_xy'8729'z'8776'z'8729'yx_412 ~v0 ~v1 v2 v3 v4 v5
  = du_xy'8729'z'8776'z'8729'yx_412 v2 v3 v4 v5
du_xy'8729'z'8776'z'8729'yx_412 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_xy'8729'z'8776'z'8729'yx_412 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
               (coe
                  MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                  (coe v0)))))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2) v3)
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1))
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_482
         (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
            (coe
               MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
               (coe v0)))
         v1 v2 v3)
      (coe
         du_x'8729'yz'8776'z'8729'yx_274 (coe v0) (coe v1) (coe v2)
         (coe v3))
-- Algebra.Properties.CommutativeSemigroup.xy∙z≈x∙zy
d_xy'8729'z'8776'x'8729'zy_426 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_xy'8729'z'8776'x'8729'zy_426 ~v0 ~v1 v2 v3 v4 v5
  = du_xy'8729'z'8776'x'8729'zy_426 v2 v3 v4 v5
du_xy'8729'z'8776'x'8729'zy_426 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_xy'8729'z'8776'x'8729'zy_426 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
               (coe
                  MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                  (coe v0)))))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2) v3)
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v2))
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_482
         (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
            (coe
               MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
               (coe v0)))
         v1 v2 v3)
      (coe
         du_x'8729'yz'8776'x'8729'zy_288 (coe v0) (coe v1) (coe v2)
         (coe v3))
-- Algebra.Properties.CommutativeSemigroup.xy∙z≈y∙zx
d_xy'8729'z'8776'y'8729'zx_440 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_xy'8729'z'8776'y'8729'zx_440 ~v0 ~v1 v2 v3 v4 v5
  = du_xy'8729'z'8776'y'8729'zx_440 v2 v3 v4 v5
du_xy'8729'z'8776'y'8729'zx_440 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_xy'8729'z'8776'y'8729'zx_440 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
               (coe
                  MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                  (coe v0)))))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2) v3)
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1))
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_482
         (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
            (coe
               MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
               (coe v0)))
         v1 v2 v3)
      (coe
         du_x'8729'yz'8776'y'8729'zx_300 (coe v0) (coe v1) (coe v2)
         (coe v3))
-- Algebra.Properties.CommutativeSemigroup.xy∙z≈z∙xy
d_xy'8729'z'8776'z'8729'xy_454 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_xy'8729'z'8776'z'8729'xy_454 ~v0 ~v1 v2 v3 v4 v5
  = du_xy'8729'z'8776'z'8729'xy_454 v2 v3 v4 v5
du_xy'8729'z'8776'z'8729'xy_454 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_xy'8729'z'8776'z'8729'xy_454 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
               (coe
                  MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                  (coe v0)))))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2) v3)
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2))
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_482
         (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
            (coe
               MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
               (coe v0)))
         v1 v2 v3)
      (coe
         du_x'8729'yz'8776'z'8729'xy_314 (coe v0) (coe v1) (coe v2)
         (coe v3))
-- Algebra.Properties.CommutativeSemigroup.xy∙z≈yx∙z
d_xy'8729'z'8776'yx'8729'z_468 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_xy'8729'z'8776'yx'8729'z_468 ~v0 ~v1 v2 v3 v4 v5
  = du_xy'8729'z'8776'yx'8729'z_468 v2 v3 v4 v5
du_xy'8729'z'8776'yx'8729'z_468 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_xy'8729'z'8776'yx'8729'z_468 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
               (coe
                  MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                  (coe v0)))))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2) v3)
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1) v3)
      (coe
         du_xy'8729'z'8776'y'8729'xz_398 (coe v0) (coe v1) (coe v2)
         (coe v3))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_36
         (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_480
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                     (coe v0)))))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1) v3)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3))
         (coe
            MAlonzo.Code.Algebra.Structures.d_assoc_482
            (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
               (coe
                  MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                  (coe v0)))
            v2 v1 v3))
-- Algebra.Properties.CommutativeSemigroup.xy∙z≈zy∙x
d_xy'8729'z'8776'zy'8729'x_482 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_xy'8729'z'8776'zy'8729'x_482 ~v0 ~v1 v2 v3 v4 v5
  = du_xy'8729'z'8776'zy'8729'x_482 v2 v3 v4 v5
du_xy'8729'z'8776'zy'8729'x_482 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_xy'8729'z'8776'zy'8729'x_482 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
               (coe
                  MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                  (coe v0)))))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2) v3)
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v2) v1)
      (coe
         du_xy'8729'z'8776'z'8729'yx_412 (coe v0) (coe v1) (coe v2)
         (coe v3))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_36
         (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_480
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                     (coe v0)))))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v2) v1)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1))
         (coe
            MAlonzo.Code.Algebra.Structures.d_assoc_482
            (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
               (coe
                  MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                  (coe v0)))
            v3 v2 v1))
-- Algebra.Properties.CommutativeSemigroup.xy∙z≈xz∙y
d_xy'8729'z'8776'xz'8729'y_496 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_xy'8729'z'8776'xz'8729'y_496 ~v0 ~v1 v2 v3 v4 v5
  = du_xy'8729'z'8776'xz'8729'y_496 v2 v3 v4 v5
du_xy'8729'z'8776'xz'8729'y_496 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_xy'8729'z'8776'xz'8729'y_496 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
               (coe
                  MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                  (coe v0)))))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2) v3)
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v2))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3) v2)
      (coe
         du_xy'8729'z'8776'x'8729'zy_426 (coe v0) (coe v1) (coe v2)
         (coe v3))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_36
         (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_480
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                     (coe v0)))))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3) v2)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v2))
         (coe
            MAlonzo.Code.Algebra.Structures.d_assoc_482
            (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
               (coe
                  MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                  (coe v0)))
            v1 v3 v2))
-- Algebra.Properties.CommutativeSemigroup.xy∙z≈yz∙x
d_xy'8729'z'8776'yz'8729'x_510 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_xy'8729'z'8776'yz'8729'x_510 ~v0 ~v1 v2 v3 v4 v5
  = du_xy'8729'z'8776'yz'8729'x_510 v2 v3 v4 v5
du_xy'8729'z'8776'yz'8729'x_510 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_xy'8729'z'8776'yz'8729'x_510 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
               (coe
                  MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                  (coe v0)))))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2) v3)
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3) v1)
      (coe
         du_xy'8729'z'8776'y'8729'zx_440 (coe v0) (coe v1) (coe v2)
         (coe v3))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_36
         (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_480
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                     (coe v0)))))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3) v1)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1))
         (coe
            MAlonzo.Code.Algebra.Structures.d_assoc_482
            (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
               (coe
                  MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                  (coe v0)))
            v2 v3 v1))
-- Algebra.Properties.CommutativeSemigroup.xy∙z≈zx∙y
d_xy'8729'z'8776'zx'8729'y_524 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_xy'8729'z'8776'zx'8729'y_524 ~v0 ~v1 v2 v3 v4 v5
  = du_xy'8729'z'8776'zx'8729'y_524 v2 v3 v4 v5
du_xy'8729'z'8776'zx'8729'y_524 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_xy'8729'z'8776'zx'8729'y_524 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
               (coe
                  MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                  (coe v0)))))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2) v3)
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1) v2)
      (coe
         du_xy'8729'z'8776'z'8729'xy_454 (coe v0) (coe v1) (coe v2)
         (coe v3))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_36
         (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_480
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                     (coe v0)))))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1) v2)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2))
         (coe
            MAlonzo.Code.Algebra.Structures.d_assoc_482
            (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
               (coe
                  MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                  (coe v0)))
            v3 v1 v2))
-- Algebra.Properties.CommutativeSemigroup.xy∙xx≈x∙yxx
d_xy'8729'xx'8776'x'8729'yxx_536 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_xy'8729'xx'8776'x'8729'yxx_536 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Structures.d_assoc_482
      (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
         (coe
            MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
            (coe v0)))
      v1 v2 (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v1)
-- Algebra.Properties.CommutativeSemigroup.semimedialˡ
d_semimedial'737'_542 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_semimedial'737'_542 ~v0 ~v1 v2 v3 v4 v5
  = du_semimedial'737'_542 v2 v3 v4 v5
du_semimedial'737'_542 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_semimedial'737'_542 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v4 v5 v6 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v1)
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2)
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v4
                         = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                             (coe v0) in
                   coe
                     (let v5
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v4) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_setoid_200
                           (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))))))))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v1)
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3)))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2)
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v4
                            = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                (coe v0) in
                      coe
                        (let v5
                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v4) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_setoid_200
                              (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))))))))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3)))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2) v3))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2)
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v4
                               = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                   (coe v0) in
                         coe
                           (let v5
                                  = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v4) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_setoid_200
                                 (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))))))))
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2) v3))
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1) v3))
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (let v4
                                  = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                      (coe v0) in
                            coe
                              (let v5
                                     = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v4) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.du_setoid_200
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))))))))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1) v3))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3)))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                              (let v4
                                     = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                         (coe v0) in
                               coe
                                 (let v5
                                        = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                                            (coe v4) in
                                  coe
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.du_setoid_200
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                          (coe v5))))))))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3)))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2)
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2)
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3))
                     (let v4
                            = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                (coe
                                   MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                   (let v4
                                          = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                              (coe v0) in
                                    coe
                                      (let v5
                                             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                                                 (coe v4) in
                                       coe
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.du_setoid_200
                                            (coe
                                               MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                               (coe v5)))))) in
                      coe
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                              (coe v4))
                           (coe
                              MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                              (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2)
                              (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3))))
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                        (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isMagma_480
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                                 (coe
                                    MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                    (coe v0)))))
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2)
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3))
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
                           (coe
                              MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
                              (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3)))
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_assoc_482
                           (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                              (coe
                                 MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                 (coe v0)))
                           v1 v2 (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3))))
                  (let v4
                         = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                             (coe v0) in
                   coe
                     (let v5
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v4) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'737'_202
                           (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))
                           (coe v1)
                           (coe
                              MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                              (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1) v3)
                           (coe
                              MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
                              (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3))
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_assoc_482
                              (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                                 (coe
                                    MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                    (coe v0)))
                              v2 v1 v3)))))
               (let v4
                      = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                          (coe v0) in
                coe
                  (let v5
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'737'_202
                        (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))
                        (coe v1)
                        (coe
                           MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                           (\ v6 -> coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v6 v3)
                           (\ v6 v7 -> v6)
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2)
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1))
                        (coe
                           MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                           (\ v6 v7 -> v7)
                           (\ v6 -> coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v6 v3)
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2)
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1))
                        (let v6
                               = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                   (coe v0) in
                         coe
                           (let v7
                                  = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v6) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'691'_206
                                 (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v7))
                                 (coe v3) (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2)
                                 (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1)
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.d_comm_558
                                    (MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                       (coe v0))
                                    v1 v2))))))))
            (let v4
                   = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                       (coe v0) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'737'_202
                     (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))
                     (coe v1)
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2) v3)
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                        (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isMagma_480
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                                 (coe
                                    MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                    (coe v0)))))
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2) v3)
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3))
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_assoc_482
                           (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                              (coe
                                 MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                 (coe v0)))
                           v1 v2 v3))))))
         (coe
            MAlonzo.Code.Algebra.Structures.d_assoc_482
            (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
               (coe
                  MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                  (coe v0)))
            v1 v1 (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3)))
-- Algebra.Properties.CommutativeSemigroup.semimedialʳ
d_semimedial'691'_550 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_semimedial'691'_550 ~v0 ~v1 v2 v3 v4 v5
  = du_semimedial'691'_550 v2 v3 v4 v5
du_semimedial'691'_550 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_semimedial'691'_550 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v4 v5 v6 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3)
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v1))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1)
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v4
                         = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                             (coe v0) in
                   coe
                     (let v5
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v4) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_setoid_200
                           (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))))))))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3)
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v1))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v1)))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1)
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v4
                            = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                (coe v0) in
                      coe
                        (let v5
                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v4) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_setoid_200
                              (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))))))))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v1)))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1) v1))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1)
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v4
                               = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                   (coe v0) in
                         coe
                           (let v5
                                  = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v4) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_setoid_200
                                 (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))))))))
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1) v1))
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3) v1))
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1)
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (let v4
                                  = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                      (coe v0) in
                            coe
                              (let v5
                                     = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v4) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.du_setoid_200
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))))))))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3) v1))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1)))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1)
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                              (let v4
                                     = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                         (coe v0) in
                               coe
                                 (let v5
                                        = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                                            (coe v4) in
                                  coe
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.du_setoid_200
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                          (coe v5))))))))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1)))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1)
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1)
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1))
                     (let v4
                            = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                (coe
                                   MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                   (let v4
                                          = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                              (coe v0) in
                                    coe
                                      (let v5
                                             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                                                 (coe v4) in
                                       coe
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.du_setoid_200
                                            (coe
                                               MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                               (coe v5)))))) in
                      coe
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                              (coe v4))
                           (coe
                              MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                              (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1)
                              (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1))))
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                        (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isMagma_480
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                                 (coe
                                    MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                    (coe v0)))))
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1)
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1))
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
                           (coe
                              MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
                              (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1)))
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_assoc_482
                           (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                              (coe
                                 MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                 (coe v0)))
                           v2 v1 (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1))))
                  (let v4
                         = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                             (coe v0) in
                   coe
                     (let v5
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v4) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'737'_202
                           (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))
                           (coe v2)
                           (coe
                              MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                              (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3) v1)
                           (coe
                              MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
                              (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1))
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_assoc_482
                              (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                                 (coe
                                    MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                    (coe v0)))
                              v1 v3 v1)))))
               (let v4
                      = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                          (coe v0) in
                coe
                  (let v5
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'737'_202
                        (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))
                        (coe v2)
                        (coe
                           MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                           (\ v6 -> coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v6 v1)
                           (\ v6 v7 -> v6)
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1)
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3))
                        (coe
                           MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                           (\ v6 v7 -> v7)
                           (\ v6 -> coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v6 v1)
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1)
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3))
                        (let v6
                               = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                   (coe v0) in
                         coe
                           (let v7
                                  = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v6) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'691'_206
                                 (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v7))
                                 (coe v1) (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1)
                                 (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3)
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.d_comm_558
                                    (MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                       (coe v0))
                                    v3 v1))))))))
            (let v4
                   = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                       (coe v0) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'737'_202
                     (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))
                     (coe v2)
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v1))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1) v1)
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                        (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isMagma_480
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                                 (coe
                                    MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                    (coe v0)))))
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1) v1)
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v1))
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_assoc_482
                           (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                              (coe
                                 MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                 (coe v0)))
                           v3 v1 v1))))))
         (coe
            MAlonzo.Code.Algebra.Structures.d_assoc_482
            (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
               (coe
                  MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                  (coe v0)))
            v2 v3 (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v1)))
-- Algebra.Properties.CommutativeSemigroup.middleSemimedial
d_middleSemimedial_564 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_middleSemimedial_564 ~v0 ~v1 v2 v3 v4 v5
  = du_middleSemimedial_564 v2 v3 v4 v5
du_middleSemimedial_564 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_middleSemimedial_564 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v4 v5 v6 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2)
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3)
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v4
                         = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                             (coe v0) in
                   coe
                     (let v5
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v4) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_setoid_200
                           (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))))))))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v2)
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1)))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3)
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v4
                            = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                (coe v0) in
                      coe
                        (let v5
                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v4) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_setoid_200
                              (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))))))))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1)))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3) v1))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3)
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v4
                               = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                   (coe v0) in
                         coe
                           (let v5
                                  = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v4) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_setoid_200
                                 (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))))))))
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3) v1))
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v2) v1))
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3)
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (let v4
                                  = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                      (coe v0) in
                            coe
                              (let v5
                                     = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v4) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.du_setoid_200
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))))))))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v2) v1))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1)))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3)
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                              (let v4
                                     = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                         (coe v0) in
                               coe
                                 (let v5
                                        = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                                            (coe v4) in
                                  coe
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.du_setoid_200
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                          (coe v5))))))))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1)))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3)
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3)
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1))
                     (let v4
                            = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                (coe
                                   MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                   (let v4
                                          = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                              (coe v0) in
                                    coe
                                      (let v5
                                             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                                                 (coe v4) in
                                       coe
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.du_setoid_200
                                            (coe
                                               MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                               (coe v5)))))) in
                      coe
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                              (coe v4))
                           (coe
                              MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                              (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3)
                              (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1))))
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                        (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isMagma_480
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                                 (coe
                                    MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                    (coe v0)))))
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1 v3)
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1))
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v1
                           (coe
                              MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3
                              (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1)))
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_assoc_482
                           (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                              (coe
                                 MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                 (coe v0)))
                           v1 v3 (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1))))
                  (let v4
                         = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                             (coe v0) in
                   coe
                     (let v5
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v4) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'737'_202
                           (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))
                           (coe v1)
                           (coe
                              MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                              (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v2) v1)
                           (coe
                              MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3
                              (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v1))
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_assoc_482
                              (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                                 (coe
                                    MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                    (coe v0)))
                              v3 v2 v1)))))
               (let v4
                      = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                          (coe v0) in
                coe
                  (let v5
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'737'_202
                        (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))
                        (coe v1)
                        (coe
                           MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                           (\ v6 -> coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v6 v1)
                           (\ v6 v7 -> v6)
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3)
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v2))
                        (coe
                           MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                           (\ v6 v7 -> v7)
                           (\ v6 -> coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v6 v1)
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3)
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v2))
                        (let v6
                               = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                   (coe v0) in
                         coe
                           (let v7
                                  = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v6) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'691'_206
                                 (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v7))
                                 (coe v1) (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3)
                                 (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v2)
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.d_comm_558
                                    (MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                       (coe v0))
                                    v2 v3))))))))
            (let v4
                   = MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                       (coe v0) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'737'_202
                     (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))
                     (coe v1)
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3) v1)
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                        (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isMagma_480
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                                 (coe
                                    MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                    (coe v0)))))
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2 v3) v1)
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v2
                           (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1))
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_assoc_482
                           (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
                              (coe
                                 MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                                 (coe v0)))
                           v2 v3 v1))))))
         (coe
            MAlonzo.Code.Algebra.Structures.d_assoc_482
            (MAlonzo.Code.Algebra.Structures.d_isSemigroup_556
               (coe
                  MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_682
                  (coe v0)))
            v1 v2 (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__680 v0 v3 v1)))
-- Algebra.Properties.CommutativeSemigroup.semimedial
d_semimedial_572 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_semimedial_572 ~v0 ~v1 v2 = du_semimedial_572 v2
du_semimedial_572 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_semimedial_572 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_semimedial'737'_542 (coe v0))
      (coe du_semimedial'691'_550 (coe v0))
