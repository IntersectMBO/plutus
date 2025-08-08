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

module MAlonzo.Code.VerifiedCompilation.UInline where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Untyped
import qualified MAlonzo.Code.Untyped.Annotation
import qualified MAlonzo.Code.Untyped.RenamingSubstitution
import qualified MAlonzo.Code.VerifiedCompilation.Equality

-- VerifiedCompilation.UInline.listWeaken
d_listWeaken_8 ::
  () ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14]
d_listWeaken_8 ~v0 v1 = du_listWeaken_8 v1
du_listWeaken_8 ::
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14]
du_listWeaken_8 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Untyped.RenamingSubstitution.du_weaken_88 (coe v1))
             (coe du_listWeaken_8 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.UInline.Bind
d_Bind_16 a0 = ()
data T_Bind_16
  = C_'9633'_18 |
    C__'44'__22 T_Bind_16 MAlonzo.Code.Untyped.T__'8866'_14
-- VerifiedCompilation.UInline.bind
d_bind_24 ::
  () -> T_Bind_16 -> MAlonzo.Code.Untyped.T__'8866'_14 -> T_Bind_16
d_bind_24 ~v0 v1 v2 = du_bind_24 v1 v2
du_bind_24 ::
  T_Bind_16 -> MAlonzo.Code.Untyped.T__'8866'_14 -> T_Bind_16
du_bind_24 v0 v1
  = coe
      C__'44'__22 v0
      (coe
         MAlonzo.Code.Untyped.RenamingSubstitution.du_weaken_88 (coe v1))
-- VerifiedCompilation.UInline.get
d_get_30 ::
  () ->
  T_Bind_16 -> AgdaAny -> Maybe MAlonzo.Code.Untyped.T__'8866'_14
d_get_30 ~v0 v1 v2 = du_get_30 v1 v2
du_get_30 ::
  T_Bind_16 -> AgdaAny -> Maybe MAlonzo.Code.Untyped.T__'8866'_14
du_get_30 v0 v1
  = case coe v0 of
      C_'9633'_18 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C__'44'__22 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
               -> let v6 = coe du_get_30 (coe v3) (coe v5) in
                  coe
                    (case coe v6 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                              (coe
                                 MAlonzo.Code.Untyped.RenamingSubstitution.du_weaken_88 (coe v7))
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v6
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.UInline.usage
d_usage_66 ::
  () ->
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  AgdaAny -> MAlonzo.Code.Untyped.T__'8866'_14 -> Integer
d_usage_66 ~v0 v1 v2 v3 = du_usage_66 v1 v2 v3
du_usage_66 ::
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  AgdaAny -> MAlonzo.Code.Untyped.T__'8866'_14 -> Integer
du_usage_66 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Untyped.C_'96'_18 v3
        -> let v4
                 = coe
                     MAlonzo.Code.VerifiedCompilation.Equality.d__'8799'__12 v0 v1 v3 in
           coe
             (case coe v4 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                  -> if coe v5
                       then coe seq (coe v6) (coe (1 :: Integer))
                       else coe seq (coe v6) (coe (0 :: Integer))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Untyped.C_ƛ_20 v3
        -> coe
             du_usage_66
             (coe
                MAlonzo.Code.VerifiedCompilation.Equality.du_DecEq'45'Maybe_122
                (coe v0))
             (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)) (coe v3)
      MAlonzo.Code.Untyped.C__'183'__22 v3 v4
        -> coe
             addInt (coe du_usage_66 (coe v0) (coe v1) (coe v3))
             (coe du_usage_66 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Untyped.C_force_24 v3
        -> coe du_usage_66 (coe v0) (coe v1) (coe v3)
      MAlonzo.Code.Untyped.C_delay_26 v3
        -> coe du_usage_66 (coe v0) (coe v1) (coe v3)
      MAlonzo.Code.Untyped.C_con_28 v3 -> coe (0 :: Integer)
      MAlonzo.Code.Untyped.C_constr_34 v3 v4
        -> coe
             MAlonzo.Code.Data.List.Base.d_sum_280
             (coe
                MAlonzo.Code.Data.List.Base.du_map_22
                (coe du_usage_66 (coe v0) (coe v1)) (coe v4))
      MAlonzo.Code.Untyped.C_case_40 v3 v4
        -> coe
             addInt
             (coe
                MAlonzo.Code.Data.List.Base.d_sum_280
                (coe
                   MAlonzo.Code.Data.List.Base.du_map_22
                   (coe du_usage_66 (coe v0) (coe v1)) (coe v4)))
             (coe du_usage_66 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Untyped.C_builtin_44 v3 -> coe (0 :: Integer)
      MAlonzo.Code.Untyped.C_error_46 -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.UInline.Inlined
d_Inlined_128 a0 a1 a2 a3 a4 a5 a6 = ()
data T_Inlined_128
  = C_sub_146 MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6
              MAlonzo.Code.Untyped.T__'8866'_14
              MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 T_Inlined_128 |
    C_c'183'_166 MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6
                 T_Inlined_128 |
    C__'183'__186 MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6
                  T_Inlined_128 T_Inlined_128 |
    C_cƛ_206 MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6
             MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 T_Inlined_128 |
    C_ƛb_222 MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6
             T_Inlined_128 |
    C_ƛ_234 MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6
            T_Inlined_128 |
    C_force_248 MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6
                T_Inlined_128 |
    C_delay_262 MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6
                T_Inlined_128 |
    C_refl_274 MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6
-- VerifiedCompilation.UInline.Inline
d_Inline_280
  = error
      "MAlonzo Runtime Error: postulate evaluated: VerifiedCompilation.UInline.Inline"
-- VerifiedCompilation.UInline.Vars
d_Vars_282
  = error
      "MAlonzo Runtime Error: postulate evaluated: VerifiedCompilation.UInline.Vars"
-- VerifiedCompilation.UInline.a
d_a_284
  = error
      "MAlonzo Runtime Error: postulate evaluated: VerifiedCompilation.UInline.a"
-- VerifiedCompilation.UInline.b
d_b_286
  = error
      "MAlonzo Runtime Error: postulate evaluated: VerifiedCompilation.UInline.b"
-- VerifiedCompilation.UInline.f
d_f_288
  = error
      "MAlonzo Runtime Error: postulate evaluated: VerifiedCompilation.UInline.f"
-- VerifiedCompilation.UInline.g
d_g_290
  = error
      "MAlonzo Runtime Error: postulate evaluated: VerifiedCompilation.UInline.g"
-- VerifiedCompilation.UInline.eqVars
d_eqVars_292
  = error
      "MAlonzo Runtime Error: postulate evaluated: VerifiedCompilation.UInline.eqVars"
-- VerifiedCompilation.UInline.Zero
d_Zero_294
  = error
      "MAlonzo Runtime Error: postulate evaluated: VerifiedCompilation.UInline.Zero"
-- VerifiedCompilation.UInline.One
d_One_296
  = error
      "MAlonzo Runtime Error: postulate evaluated: VerifiedCompilation.UInline.One"
-- VerifiedCompilation.UInline.Two
d_Two_298
  = error
      "MAlonzo Runtime Error: postulate evaluated: VerifiedCompilation.UInline.Two"
-- VerifiedCompilation.UInline.EqVars
d_EqVars_300 :: MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6
d_EqVars_300 = coe d_eqVars_292
-- VerifiedCompilation.UInline.beforeEx1
d_beforeEx1_302 :: MAlonzo.Code.Untyped.T__'8866'_14
d_beforeEx1_302
  = coe
      MAlonzo.Code.Untyped.C__'183'__22
      (coe
         MAlonzo.Code.Untyped.C__'183'__22
         (coe
            MAlonzo.Code.Untyped.C_ƛ_20
            (coe
               MAlonzo.Code.Untyped.C_ƛ_20
               (coe
                  MAlonzo.Code.Untyped.C__'183'__22
                  (coe
                     MAlonzo.Code.Untyped.C_'96'_18
                     (coe
                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                        (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))
                  (coe
                     MAlonzo.Code.Untyped.C_'96'_18
                     (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))))
         (coe MAlonzo.Code.Untyped.C_'96'_18 (coe d_a_284)))
      (coe MAlonzo.Code.Untyped.C_'96'_18 (coe d_b_286))
-- VerifiedCompilation.UInline.uncleanEx1
d_uncleanEx1_304 :: MAlonzo.Code.Untyped.T__'8866'_14
d_uncleanEx1_304
  = coe
      MAlonzo.Code.Untyped.C__'183'__22
      (coe
         MAlonzo.Code.Untyped.C__'183'__22
         (coe
            MAlonzo.Code.Untyped.C_ƛ_20
            (coe
               MAlonzo.Code.Untyped.C_ƛ_20
               (coe
                  MAlonzo.Code.Untyped.C__'183'__22
                  (coe
                     MAlonzo.Code.Untyped.RenamingSubstitution.du_weaken_88
                     (coe
                        MAlonzo.Code.Untyped.RenamingSubstitution.du_weaken_88
                        (coe MAlonzo.Code.Untyped.C_'96'_18 (coe d_a_284))))
                  (coe
                     MAlonzo.Code.Untyped.RenamingSubstitution.du_weaken_88
                     (coe
                        MAlonzo.Code.Untyped.RenamingSubstitution.du_weaken_88
                        (coe MAlonzo.Code.Untyped.C_'96'_18 (coe d_b_286)))))))
         (coe MAlonzo.Code.Untyped.C_'96'_18 (coe d_a_284)))
      (coe MAlonzo.Code.Untyped.C_'96'_18 (coe d_b_286))
-- VerifiedCompilation.UInline.afterEx1
d_afterEx1_306 :: MAlonzo.Code.Untyped.T__'8866'_14
d_afterEx1_306
  = coe
      MAlonzo.Code.Untyped.C__'183'__22
      (coe MAlonzo.Code.Untyped.C_'96'_18 (coe d_a_284))
      (coe MAlonzo.Code.Untyped.C_'96'_18 (coe d_b_286))
-- VerifiedCompilation.UInline.beforeEx2
d_beforeEx2_308 :: MAlonzo.Code.Untyped.T__'8866'_14
d_beforeEx2_308
  = coe
      MAlonzo.Code.Untyped.C__'183'__22
      (coe
         MAlonzo.Code.Untyped.C_ƛ_20
         (coe
            MAlonzo.Code.Untyped.C__'183'__22
            (coe
               MAlonzo.Code.Untyped.C__'183'__22
               (coe
                  MAlonzo.Code.Untyped.C_'96'_18
                  (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe d_f_288)))
               (coe
                  MAlonzo.Code.Untyped.C__'183'__22
                  (coe
                     MAlonzo.Code.Untyped.C__'183'__22
                     (coe
                        MAlonzo.Code.Untyped.C_'96'_18
                        (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                     (coe MAlonzo.Code.Untyped.C_con_28 (coe d_Zero_294)))
                  (coe MAlonzo.Code.Untyped.C_con_28 (coe d_One_296))))
            (coe
               MAlonzo.Code.Untyped.C__'183'__22
               (coe
                  MAlonzo.Code.Untyped.C_'96'_18
                  (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
               (coe MAlonzo.Code.Untyped.C_con_28 (coe d_Two_298)))))
      (coe MAlonzo.Code.Untyped.C_'96'_18 (coe d_g_290))
-- VerifiedCompilation.UInline.afterEx2
d_afterEx2_310 :: MAlonzo.Code.Untyped.T__'8866'_14
d_afterEx2_310
  = coe
      MAlonzo.Code.Untyped.C__'183'__22
      (coe
         MAlonzo.Code.Untyped.C_ƛ_20
         (coe
            MAlonzo.Code.Untyped.C__'183'__22
            (coe
               MAlonzo.Code.Untyped.C__'183'__22
               (coe
                  MAlonzo.Code.Untyped.C_'96'_18
                  (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe d_f_288)))
               (coe
                  MAlonzo.Code.Untyped.C__'183'__22
                  (coe
                     MAlonzo.Code.Untyped.C__'183'__22
                     (coe
                        MAlonzo.Code.Untyped.C_'96'_18
                        (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe d_g_290)))
                     (coe MAlonzo.Code.Untyped.C_con_28 (coe d_Zero_294)))
                  (coe MAlonzo.Code.Untyped.C_con_28 (coe d_One_296))))
            (coe
               MAlonzo.Code.Untyped.C__'183'__22
               (coe
                  MAlonzo.Code.Untyped.C_'96'_18
                  (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
               (coe MAlonzo.Code.Untyped.C_con_28 (coe d_Two_298)))))
      (coe MAlonzo.Code.Untyped.C_'96'_18 (coe d_g_290))
-- VerifiedCompilation.UInline.Ex3Vars
d_Ex3Vars_312 :: ()
d_Ex3Vars_312 = erased
-- VerifiedCompilation.UInline.beforeEx3
d_beforeEx3_314 :: MAlonzo.Code.Untyped.T__'8866'_14
d_beforeEx3_314
  = coe
      MAlonzo.Code.Untyped.C__'183'__22
      (coe
         MAlonzo.Code.Untyped.C_ƛ_20
         (coe
            MAlonzo.Code.Untyped.C__'183'__22
            (coe
               MAlonzo.Code.Untyped.C_ƛ_20
               (coe
                  MAlonzo.Code.Untyped.C__'183'__22
                  (coe
                     MAlonzo.Code.Untyped.C_'96'_18
                     (coe
                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                        (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))
                  (coe
                     MAlonzo.Code.Untyped.C_'96'_18
                     (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))))
            (coe
               MAlonzo.Code.Untyped.C_'96'_18
               (coe
                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                  (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))))
      (coe
         MAlonzo.Code.Untyped.C_'96'_18
         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
-- VerifiedCompilation.UInline.afterEx3
d_afterEx3_316 :: MAlonzo.Code.Untyped.T__'8866'_14
d_afterEx3_316
  = coe
      MAlonzo.Code.Untyped.C__'183'__22
      (coe
         MAlonzo.Code.Untyped.C_ƛ_20
         (coe
            MAlonzo.Code.Untyped.C__'183'__22
            (coe
               MAlonzo.Code.Untyped.C_'96'_18
               (coe
                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                  (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))
            (coe
               MAlonzo.Code.Untyped.C_'96'_18
               (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))))
      (coe
         MAlonzo.Code.Untyped.C_'96'_18
         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
-- VerifiedCompilation.UInline.callsiteInlineBefore
d_callsiteInlineBefore_318 :: MAlonzo.Code.Untyped.T__'8866'_14
d_callsiteInlineBefore_318
  = coe
      MAlonzo.Code.Untyped.C__'183'__22
      (coe
         MAlonzo.Code.Untyped.C_ƛ_20
         (coe
            MAlonzo.Code.Untyped.C__'183'__22
            (coe
               MAlonzo.Code.Untyped.C__'183'__22
               (coe
                  MAlonzo.Code.Untyped.RenamingSubstitution.du_weaken_88
                  (coe MAlonzo.Code.Untyped.C_'96'_18 (coe d_f_288)))
               (coe
                  MAlonzo.Code.Untyped.C__'183'__22
                  (coe
                     MAlonzo.Code.Untyped.C__'183'__22
                     (coe
                        MAlonzo.Code.Untyped.C_'96'_18
                        (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                     (coe MAlonzo.Code.Untyped.C_con_28 (coe d_Zero_294)))
                  (coe MAlonzo.Code.Untyped.C_con_28 (coe d_One_296))))
            (coe
               MAlonzo.Code.Untyped.C__'183'__22
               (coe
                  MAlonzo.Code.Untyped.C_'96'_18
                  (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
               (coe MAlonzo.Code.Untyped.C_con_28 (coe d_Two_298)))))
      (coe
         MAlonzo.Code.Untyped.C_ƛ_20
         (coe
            MAlonzo.Code.Untyped.C_ƛ_20
            (coe
               MAlonzo.Code.Untyped.C__'183'__22
               (coe
                  MAlonzo.Code.Untyped.C__'183'__22
                  (coe
                     MAlonzo.Code.Untyped.RenamingSubstitution.du_weaken_88
                     (coe
                        MAlonzo.Code.Untyped.RenamingSubstitution.du_weaken_88
                        (coe MAlonzo.Code.Untyped.C_'96'_18 (coe d_g_290))))
                  (coe
                     MAlonzo.Code.Untyped.C_'96'_18
                     (coe
                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                        (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))))
               (coe
                  MAlonzo.Code.Untyped.C_'96'_18
                  (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))))
-- VerifiedCompilation.UInline.callsiteInlineAfter
d_callsiteInlineAfter_320 :: MAlonzo.Code.Untyped.T__'8866'_14
d_callsiteInlineAfter_320
  = coe
      MAlonzo.Code.Untyped.C__'183'__22
      (coe
         MAlonzo.Code.Untyped.C_ƛ_20
         (coe
            MAlonzo.Code.Untyped.C__'183'__22
            (coe
               MAlonzo.Code.Untyped.C__'183'__22
               (coe
                  MAlonzo.Code.Untyped.RenamingSubstitution.du_weaken_88
                  (coe MAlonzo.Code.Untyped.C_'96'_18 (coe d_f_288)))
               (coe
                  MAlonzo.Code.Untyped.C__'183'__22
                  (coe
                     MAlonzo.Code.Untyped.C__'183'__22
                     (coe
                        MAlonzo.Code.Untyped.RenamingSubstitution.du_weaken_88
                        (coe
                           MAlonzo.Code.Untyped.C_ƛ_20
                           (coe
                              MAlonzo.Code.Untyped.C_ƛ_20
                              (coe
                                 MAlonzo.Code.Untyped.C__'183'__22
                                 (coe
                                    MAlonzo.Code.Untyped.C__'183'__22
                                    (coe
                                       MAlonzo.Code.Untyped.RenamingSubstitution.du_weaken_88
                                       (coe
                                          MAlonzo.Code.Untyped.RenamingSubstitution.du_weaken_88
                                          (coe MAlonzo.Code.Untyped.C_'96'_18 (coe d_g_290))))
                                    (coe
                                       MAlonzo.Code.Untyped.C_'96'_18
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                          (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))))
                                 (coe
                                    MAlonzo.Code.Untyped.C_'96'_18
                                    (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))))))
                     (coe MAlonzo.Code.Untyped.C_con_28 (coe d_Zero_294)))
                  (coe MAlonzo.Code.Untyped.C_con_28 (coe d_One_296))))
            (coe
               MAlonzo.Code.Untyped.C__'183'__22
               (coe
                  MAlonzo.Code.Untyped.C_'96'_18
                  (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
               (coe MAlonzo.Code.Untyped.C_con_28 (coe d_Two_298)))))
      (coe
         MAlonzo.Code.Untyped.C_ƛ_20
         (coe
            MAlonzo.Code.Untyped.C_ƛ_20
            (coe
               MAlonzo.Code.Untyped.C__'183'__22
               (coe
                  MAlonzo.Code.Untyped.C__'183'__22
                  (coe
                     MAlonzo.Code.Untyped.RenamingSubstitution.du_weaken_88
                     (coe
                        MAlonzo.Code.Untyped.RenamingSubstitution.du_weaken_88
                        (coe MAlonzo.Code.Untyped.C_'96'_18 (coe d_g_290))))
                  (coe
                     MAlonzo.Code.Untyped.C_'96'_18
                     (coe
                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                        (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))))
               (coe
                  MAlonzo.Code.Untyped.C_'96'_18
                  (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))))
-- VerifiedCompilation.UInline.callsiteInlineFinal
d_callsiteInlineFinal_322 :: MAlonzo.Code.Untyped.T__'8866'_14
d_callsiteInlineFinal_322
  = coe
      MAlonzo.Code.Untyped.C__'183'__22
      (coe
         MAlonzo.Code.Untyped.C__'183'__22
         (coe MAlonzo.Code.Untyped.C_'96'_18 (coe d_f_288))
         (coe
            MAlonzo.Code.Untyped.C__'183'__22
            (coe
               MAlonzo.Code.Untyped.C__'183'__22
               (coe MAlonzo.Code.Untyped.C_'96'_18 (coe d_g_290))
               (coe MAlonzo.Code.Untyped.C_con_28 (coe d_Zero_294)))
            (coe MAlonzo.Code.Untyped.C_con_28 (coe d_One_296))))
      (coe
         MAlonzo.Code.Untyped.C_ƛ_20
         (coe
            MAlonzo.Code.Untyped.C__'183'__22
            (coe
               MAlonzo.Code.Untyped.C__'183'__22
               (coe
                  MAlonzo.Code.Untyped.C_'96'_18
                  (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe d_g_290)))
               (coe MAlonzo.Code.Untyped.C_con_28 (coe d_Two_298)))
            (coe
               MAlonzo.Code.Untyped.C_'96'_18
               (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))))
-- VerifiedCompilation.UInline.isInline?
d_isInline'63'_332
  = error
      "MAlonzo Runtime Error: postulate evaluated: VerifiedCompilation.UInline.isInline?"
