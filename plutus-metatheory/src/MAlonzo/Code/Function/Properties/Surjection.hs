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

module MAlonzo.Code.Function.Properties.Surjection where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Function.Bundles qualified
import MAlonzo.Code.Function.Construct.Composition qualified
import MAlonzo.Code.Function.Construct.Identity qualified
import MAlonzo.Code.Function.Structures qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties qualified
import MAlonzo.Code.Relation.Binary.Reasoning.Base.Single qualified
import MAlonzo.Code.Relation.Binary.Reasoning.Syntax qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Function.Properties.Surjection._.Eq₁._≈_
d__'8776'__40 ::
  T_GeneralizeTel_423 ->
  MAlonzo.Code.Function.Bundles.T_Func_714 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__40 = erased
-- Function.Properties.Surjection._.Eq₂._≈_
d__'8776'__64 ::
  T_GeneralizeTel_423 ->
  MAlonzo.Code.Function.Bundles.T_Func_714 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__64 = erased
-- Function.Properties.Surjection.mkSurjection
d_mkSurjection_86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Func_714 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846
d_mkSurjection_86 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du_mkSurjection_86 v6 v7
du_mkSurjection_86 ::
  MAlonzo.Code.Function.Bundles.T_Func_714 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846
du_mkSurjection_86 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_Surjection'46'constructor_11197
      (coe MAlonzo.Code.Function.Bundles.d_to_720 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_cong_722 (coe v0)) (coe v1)
-- Function.Properties.Surjection.↠⇒⟶
d_'8608''8658''10230'_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  MAlonzo.Code.Function.Bundles.T_Func_714
d_'8608''8658''10230'_150 ~v0 ~v1 ~v2 ~v3
  = du_'8608''8658''10230'_150
du_'8608''8658''10230'_150 ::
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  MAlonzo.Code.Function.Bundles.T_Func_714
du_'8608''8658''10230'_150
  = coe MAlonzo.Code.Function.Bundles.du_function_860
-- Function.Properties.Surjection.↠⇒↪
d_'8608''8658''8618'_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880
d_'8608''8658''8618'_152 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8608''8658''8618'_152 v4
du_'8608''8658''8618'_152 ::
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880
du_'8608''8658''8618'_152 v0
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8618'_2320
      (coe
         (\ v1 ->
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
              (coe
                 MAlonzo.Code.Function.Structures.du_strictlySurjective_230
                 (coe
                    MAlonzo.Code.Function.Bundles.du_isSurjection_914
                    (coe
                       MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
                    (coe
                       MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
                    (coe v0))
                 (coe v1))))
      (coe MAlonzo.Code.Function.Bundles.d_to_854 (coe v0)) erased
-- Function.Properties.Surjection._..extendedlambda0
d_'46'extendedlambda0_228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'46'extendedlambda0_228 = erased
-- Function.Properties.Surjection.↠⇒⇔
d_'8608''8658''8660'_230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714
d_'8608''8658''8660'_230 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8608''8658''8660'_230 v4
du_'8608''8658''8660'_230 ::
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714
du_'8608''8658''8660'_230 v0
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8660'_2298
      (coe MAlonzo.Code.Function.Bundles.d_to_854 (coe v0))
      (coe
         (\ v1 ->
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
              (coe MAlonzo.Code.Function.Bundles.d_surjective_858 v0 v1)))
-- Function.Properties.Surjection.refl
d_refl_306 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846
d_refl_306 ~v0 ~v1 ~v2 = du_refl_306
du_refl_306 :: MAlonzo.Code.Function.Bundles.T_Surjection_846
du_refl_306
  = coe MAlonzo.Code.Function.Construct.Identity.du_surjection_786
-- Function.Properties.Surjection.trans
d_trans_310 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846
d_trans_310 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 = du_trans_310
du_trans_310 ::
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846
du_trans_310
  = coe
      MAlonzo.Code.Function.Construct.Composition.du_surjection_1460
-- Function.Properties.Surjection._.to⁻
d_to'8315'_330 ::
  T_GeneralizeTel_9221 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  AgdaAny -> AgdaAny
d_to'8315'_330 ~v0 v1 = du_to'8315'_330 v1
du_to'8315'_330 ::
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  AgdaAny -> AgdaAny
du_to'8315'_330 v0
  = coe MAlonzo.Code.Function.Bundles.du_to'8315'_920 (coe v0)
-- Function.Properties.Surjection._.Eq₁._≈_
d__'8776'__336 ::
  T_GeneralizeTel_9221 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__336 = erased
-- Function.Properties.Surjection._.Eq₂._≈_
d__'8776'__360 ::
  T_GeneralizeTel_9221 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__360 = erased
-- Function.Properties.Surjection.injective⇒to⁻-cong
d_injective'8658'to'8315''45'cong_382 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective'8658'to'8315''45'cong_382 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 v7
                                      v8 v9 v10
  = du_injective'8658'to'8315''45'cong_382 v2 v5 v6 v7 v8 v9 v10
du_injective'8658'to'8315''45'cong_382 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_injective'8658'to'8315''45'cong_382 v0 v1 v2 v3 v4 v5 v6
  = coe
      v3
      (coe
         MAlonzo.Code.Function.Bundles.du_to'8315'_920 (coe v2) (coe v4))
      (coe
         MAlonzo.Code.Function.Bundles.du_to'8315'_920 (coe v2) (coe v5))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (\ v7 v8 v9 ->
            coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v9)
         (coe
            MAlonzo.Code.Function.Bundles.d_to_854 v2
            (coe
               MAlonzo.Code.Function.Bundles.du_to'8315'_920 (coe v2) (coe v4)))
         (coe
            MAlonzo.Code.Function.Bundles.d_to_854 v2
            (coe
               MAlonzo.Code.Function.Bundles.du_to'8315'_920 (coe v2) (coe v5)))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1))))
            (coe
               MAlonzo.Code.Function.Bundles.d_to_854 v2
               (coe
                  MAlonzo.Code.Function.Bundles.du_to'8315'_920 (coe v2) (coe v4)))
            v4
            (coe
               MAlonzo.Code.Function.Bundles.d_to_854 v2
               (coe
                  MAlonzo.Code.Function.Bundles.du_to'8315'_920 (coe v2) (coe v5)))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1))))
               v4 v5
               (coe
                  MAlonzo.Code.Function.Bundles.d_to_854 v2
                  (coe
                     MAlonzo.Code.Function.Bundles.du_to'8315'_920 (coe v2) (coe v5)))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1))))
                  (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1)))
                  v5
                  (coe
                     MAlonzo.Code.Function.Bundles.d_to_854 v2
                     (coe
                        MAlonzo.Code.Function.Bundles.du_to'8315'_920 (coe v2) (coe v5)))
                  (coe
                     MAlonzo.Code.Function.Bundles.d_to_854 v2
                     (coe
                        MAlonzo.Code.Function.Bundles.du_to'8315'_920 (coe v2) (coe v5)))
                  (let v7
                         = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                             (coe
                                MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                (coe v1)) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                           (coe v7))
                        (coe
                           MAlonzo.Code.Function.Bundles.d_to_854 v2
                           (coe
                              MAlonzo.Code.Function.Bundles.du_to'8315'_920 (coe v2) (coe v5)))))
                  (coe
                     MAlonzo.Code.Function.Bundles.du_to'8728'to'8315'_924 (coe v0)
                     (coe v1) (coe v2) (coe v5)))
               v6)
            (coe
               MAlonzo.Code.Function.Bundles.du_to'8728'to'8315'_924 (coe v0)
               (coe v1) (coe v2) (coe v4))))
-- Function.Properties.Surjection..generalizedField-S.a
d_'46'generalizedField'45'S'46'a_411 ::
  T_GeneralizeTel_423 -> MAlonzo.Code.Agda.Primitive.T_Level_18
d_'46'generalizedField'45'S'46'a_411 v0
  = case coe v0 of
      C_mkGeneralizeTel_425 v1 v2 v3 v4 v5 v6 -> coe v1
      _                                       -> MAlonzo.RTE.mazUnreachableError
-- Function.Properties.Surjection..generalizedField-S.ℓ
d_'46'generalizedField'45'S'46'ℓ_413 ::
  T_GeneralizeTel_423 -> MAlonzo.Code.Agda.Primitive.T_Level_18
d_'46'generalizedField'45'S'46'ℓ_413 v0
  = case coe v0 of
      C_mkGeneralizeTel_425 v1 v2 v3 v4 v5 v6 -> coe v2
      _                                       -> MAlonzo.RTE.mazUnreachableError
-- Function.Properties.Surjection..generalizedField-S
d_'46'generalizedField'45'S_415 ::
  T_GeneralizeTel_423 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_'46'generalizedField'45'S_415 v0
  = case coe v0 of
      C_mkGeneralizeTel_425 v1 v2 v3 v4 v5 v6 -> coe v3
      _                                       -> MAlonzo.RTE.mazUnreachableError
-- Function.Properties.Surjection..generalizedField-T.a
d_'46'generalizedField'45'T'46'a_417 ::
  T_GeneralizeTel_423 -> MAlonzo.Code.Agda.Primitive.T_Level_18
d_'46'generalizedField'45'T'46'a_417 v0
  = case coe v0 of
      C_mkGeneralizeTel_425 v1 v2 v3 v4 v5 v6 -> coe v4
      _                                       -> MAlonzo.RTE.mazUnreachableError
-- Function.Properties.Surjection..generalizedField-T.ℓ
d_'46'generalizedField'45'T'46'ℓ_419 ::
  T_GeneralizeTel_423 -> MAlonzo.Code.Agda.Primitive.T_Level_18
d_'46'generalizedField'45'T'46'ℓ_419 v0
  = case coe v0 of
      C_mkGeneralizeTel_425 v1 v2 v3 v4 v5 v6 -> coe v5
      _                                       -> MAlonzo.RTE.mazUnreachableError
-- Function.Properties.Surjection..generalizedField-T
d_'46'generalizedField'45'T_421 ::
  T_GeneralizeTel_423 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_'46'generalizedField'45'T_421 v0
  = case coe v0 of
      C_mkGeneralizeTel_425 v1 v2 v3 v4 v5 v6 -> coe v6
      _                                       -> MAlonzo.RTE.mazUnreachableError
-- Function.Properties.Surjection.GeneralizeTel
d_GeneralizeTel_423 = ()
data T_GeneralizeTel_423
  = C_mkGeneralizeTel_425 MAlonzo.Code.Agda.Primitive.T_Level_18
                          MAlonzo.Code.Agda.Primitive.T_Level_18
                          MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
                          MAlonzo.Code.Agda.Primitive.T_Level_18
                          MAlonzo.Code.Agda.Primitive.T_Level_18
                          MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
-- Function.Properties.Surjection..generalizedField-S.a
d_'46'generalizedField'45'S'46'a_9209 ::
  T_GeneralizeTel_9221 -> MAlonzo.Code.Agda.Primitive.T_Level_18
d_'46'generalizedField'45'S'46'a_9209 v0
  = case coe v0 of
      C_mkGeneralizeTel_9223 v1 v2 v3 v4 v5 v6 -> coe v1
      _                                        -> MAlonzo.RTE.mazUnreachableError
-- Function.Properties.Surjection..generalizedField-S.ℓ
d_'46'generalizedField'45'S'46'ℓ_9211 ::
  T_GeneralizeTel_9221 -> MAlonzo.Code.Agda.Primitive.T_Level_18
d_'46'generalizedField'45'S'46'ℓ_9211 v0
  = case coe v0 of
      C_mkGeneralizeTel_9223 v1 v2 v3 v4 v5 v6 -> coe v2
      _                                        -> MAlonzo.RTE.mazUnreachableError
-- Function.Properties.Surjection..generalizedField-S
d_'46'generalizedField'45'S_9213 ::
  T_GeneralizeTel_9221 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_'46'generalizedField'45'S_9213 v0
  = case coe v0 of
      C_mkGeneralizeTel_9223 v1 v2 v3 v4 v5 v6 -> coe v3
      _                                        -> MAlonzo.RTE.mazUnreachableError
-- Function.Properties.Surjection..generalizedField-T.a
d_'46'generalizedField'45'T'46'a_9215 ::
  T_GeneralizeTel_9221 -> MAlonzo.Code.Agda.Primitive.T_Level_18
d_'46'generalizedField'45'T'46'a_9215 v0
  = case coe v0 of
      C_mkGeneralizeTel_9223 v1 v2 v3 v4 v5 v6 -> coe v4
      _                                        -> MAlonzo.RTE.mazUnreachableError
-- Function.Properties.Surjection..generalizedField-T.ℓ
d_'46'generalizedField'45'T'46'ℓ_9217 ::
  T_GeneralizeTel_9221 -> MAlonzo.Code.Agda.Primitive.T_Level_18
d_'46'generalizedField'45'T'46'ℓ_9217 v0
  = case coe v0 of
      C_mkGeneralizeTel_9223 v1 v2 v3 v4 v5 v6 -> coe v5
      _                                        -> MAlonzo.RTE.mazUnreachableError
-- Function.Properties.Surjection..generalizedField-T
d_'46'generalizedField'45'T_9219 ::
  T_GeneralizeTel_9221 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_'46'generalizedField'45'T_9219 v0
  = case coe v0 of
      C_mkGeneralizeTel_9223 v1 v2 v3 v4 v5 v6 -> coe v6
      _                                        -> MAlonzo.RTE.mazUnreachableError
-- Function.Properties.Surjection.GeneralizeTel
d_GeneralizeTel_9221 = ()
data T_GeneralizeTel_9221
  = C_mkGeneralizeTel_9223 MAlonzo.Code.Agda.Primitive.T_Level_18
                           MAlonzo.Code.Agda.Primitive.T_Level_18
                           MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
                           MAlonzo.Code.Agda.Primitive.T_Level_18
                           MAlonzo.Code.Agda.Primitive.T_Level_18
                           MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
