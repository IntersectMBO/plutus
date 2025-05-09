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

module MAlonzo.Code.Function.Properties.Bijection where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Function.Bundles qualified
import MAlonzo.Code.Function.Construct.Composition qualified
import MAlonzo.Code.Function.Construct.Identity qualified
import MAlonzo.Code.Function.Construct.Symmetry qualified
import MAlonzo.Code.Function.Properties.Inverse qualified
import MAlonzo.Code.Function.Properties.Surjection qualified
import MAlonzo.Code.Function.Structures qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Function.Properties.Bijection.refl
d_refl_28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926
d_refl_28 ~v0 ~v1 ~v2 = du_refl_28
du_refl_28 :: MAlonzo.Code.Function.Bundles.T_Bijection_926
du_refl_28
  = coe MAlonzo.Code.Function.Construct.Identity.du_bijection_788
-- Function.Properties.Bijection.sym-≡
d_sym'45''8801'_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926
d_sym'45''8801'_30 ~v0 ~v1 v2 ~v3 ~v4 = du_sym'45''8801'_30 v2
du_sym'45''8801'_30 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926
du_sym'45''8801'_30 v0
  = coe
      MAlonzo.Code.Function.Construct.Symmetry.du_bijection'45''8801'_722
      (coe v0)
-- Function.Properties.Bijection.trans
d_trans_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926
d_trans_32 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 = du_trans_32
du_trans_32 ::
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926
du_trans_32
  = coe MAlonzo.Code.Function.Construct.Composition.du_bijection_1606
-- Function.Properties.Bijection.⤖-isEquivalence
d_'10518''45'isEquivalence_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_'10518''45'isEquivalence_34 ~v0 = du_'10518''45'isEquivalence_34
du_'10518''45'isEquivalence_34 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_'10518''45'isEquivalence_34
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsEquivalence'46'constructor_745
      (coe (\ v0 -> coe du_refl_28))
      (coe
         (\ v0 v1 ->
            coe
              du_sym'45''8801'_30
              (coe
                 MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)))
      (coe (\ v0 v1 v2 -> coe du_trans_32))
-- Function.Properties.Bijection.Bijection⇒Inverse
d_Bijection'8658'Inverse_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_Bijection'8658'Inverse_36 ~v0 ~v1 v2 ~v3 ~v4 v5 v6
  = du_Bijection'8658'Inverse_36 v2 v5 v6
du_Bijection'8658'Inverse_36 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_Bijection'8658'Inverse_36 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Bundles.C_Inverse'46'constructor_38621
      (coe MAlonzo.Code.Function.Bundles.d_to_934 (coe v2))
      (coe
         MAlonzo.Code.Function.Bundles.du_to'8315'_920
         (coe MAlonzo.Code.Function.Bundles.du_surjection_946 (coe v2)))
      (coe MAlonzo.Code.Function.Bundles.d_cong_936 (coe v2))
      (coe
         MAlonzo.Code.Function.Properties.Surjection.du_injective'8658'to'8315''45'cong_382
         (coe v0) (coe v1)
         (coe MAlonzo.Code.Function.Bundles.du_surjection_946 (coe v2))
         (coe MAlonzo.Code.Function.Bundles.du_injective_940 (coe v2)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            (\ v3 v4 v5 ->
               let v6
                     = coe
                         MAlonzo.Code.Function.Bundles.du_isBijection_960 (coe v0) (coe v1)
                         (coe v2) in
               coe
                 (let v7
                        = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v6) in
                  coe
                    (let v8
                           = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v7) in
                     coe
                       (let v9
                              = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v8) in
                        coe
                          (coe
                             MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                             (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v9))
                             (coe MAlonzo.Code.Function.Bundles.d_to_934 v2 v4)
                             (coe
                                MAlonzo.Code.Function.Bundles.d_to_934 v2
                                (coe
                                   MAlonzo.Code.Function.Bundles.du_to'8315'_920
                                   (coe MAlonzo.Code.Function.Bundles.du_surjection_946 (coe v2))
                                   (coe v3)))
                             v3
                             (coe
                                MAlonzo.Code.Function.Bundles.d_cong_936 v2 v4
                                (coe
                                   MAlonzo.Code.Function.Bundles.du_to'8315'_920
                                   (coe MAlonzo.Code.Function.Bundles.du_surjection_946 (coe v2))
                                   (coe v3))
                                v5)
                             (coe
                                du_to'8728'to'8315'_118 (coe v0) (coe v1) (coe v2) (coe v3))))))))
         (coe
            (\ v3 v4 v5 ->
               coe
                 MAlonzo.Code.Function.Bundles.du_injective_940 v2
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                    (let v6
                           = coe MAlonzo.Code.Function.Bundles.du_surjection_946 (coe v2) in
                     coe
                       (coe
                          MAlonzo.Code.Function.Structures.du_strictlySurjective_230
                          (coe
                             MAlonzo.Code.Function.Bundles.du_isSurjection_914 (coe v0) (coe v1)
                             (coe v6))
                          (coe v4))))
                 v3
                 (let v6
                        = coe
                            MAlonzo.Code.Function.Bundles.du_isBijection_960 (coe v0) (coe v1)
                            (coe v2) in
                  coe
                    (let v7
                           = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v6) in
                     coe
                       (let v8
                              = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v7) in
                        coe
                          (let v9
                                 = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v8) in
                           coe
                             (coe
                                MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v9))
                                (coe
                                   MAlonzo.Code.Function.Bundles.d_to_934 v2
                                   (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (let v10
                                             = coe
                                                 MAlonzo.Code.Function.Bundles.du_surjection_946
                                                 (coe v2) in
                                       coe
                                         (coe
                                            MAlonzo.Code.Function.Structures.du_strictlySurjective_230
                                            (coe
                                               MAlonzo.Code.Function.Bundles.du_isSurjection_914
                                               (coe v0) (coe v1) (coe v10))
                                            (coe v4)))))
                                v4 (coe MAlonzo.Code.Function.Bundles.d_to_934 v2 v3)
                                (coe du_to'8728'to'8315'_118 (coe v0) (coe v1) (coe v2) (coe v4))
                                v5))))))))
-- Function.Properties.Bijection._.to∘to⁻
d_to'8728'to'8315'_118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926 -> AgdaAny -> AgdaAny
d_to'8728'to'8315'_118 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 v7
  = du_to'8728'to'8315'_118 v2 v5 v6 v7
du_to'8728'to'8315'_118 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926 -> AgdaAny -> AgdaAny
du_to'8728'to'8315'_118 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (let v4
             = coe MAlonzo.Code.Function.Bundles.du_surjection_946 (coe v2) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.du_strictlySurjective_230
            (coe
               MAlonzo.Code.Function.Bundles.du_isSurjection_914 (coe v0) (coe v1)
               (coe v4))
            (coe v3)))
-- Function.Properties.Bijection.Bijection⇒Equivalence
d_Bijection'8658'Equivalence_124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714
d_Bijection'8658'Equivalence_124 ~v0 ~v1 v2 ~v3 ~v4 v5 v6
  = du_Bijection'8658'Equivalence_124 v2 v5 v6
du_Bijection'8658'Equivalence_124 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714
du_Bijection'8658'Equivalence_124 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Properties.Inverse.du_Inverse'8658'Equivalence_552
      (coe du_Bijection'8658'Inverse_36 (coe v0) (coe v1) (coe v2))
-- Function.Properties.Bijection.⤖⇒↔
d_'10518''8658''8596'_126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_'10518''8658''8596'_126 ~v0 ~v1 ~v2 ~v3
  = du_'10518''8658''8596'_126
du_'10518''8658''8596'_126 ::
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_'10518''8658''8596'_126
  = coe
      du_Bijection'8658'Inverse_36
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
-- Function.Properties.Bijection.⤖⇒⇔
d_'10518''8658''8660'_128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714
d_'10518''8658''8660'_128 ~v0 ~v1 ~v2 ~v3
  = du_'10518''8658''8660'_128
du_'10518''8658''8660'_128 ::
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714
du_'10518''8658''8660'_128
  = coe
      du_Bijection'8658'Equivalence_124
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
