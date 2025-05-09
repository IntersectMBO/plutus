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

module MAlonzo.Code.VerifiedCompilation.UForceDelay where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Maybe qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Data.Irrelevant qualified
import MAlonzo.Code.Data.Nat.Properties qualified
import MAlonzo.Code.Relation.Nullary.Decidable.Core qualified
import MAlonzo.Code.Relation.Nullary.Reflects qualified
import MAlonzo.Code.Untyped qualified
import MAlonzo.Code.Untyped.RenamingSubstitution qualified
import MAlonzo.Code.VerifiedCompilation.Certificate qualified
import MAlonzo.Code.VerifiedCompilation.Equality qualified
import MAlonzo.Code.VerifiedCompilation.UntypedTranslation qualified
import MAlonzo.Code.VerifiedCompilation.UntypedViews qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- VerifiedCompilation.UForceDelay.pureFD
d_pureFD_8 a0 a1 a2 a3 = ()
data T_pureFD_8
  = C_forcedelay_18 T_pureFD_8 | C_pushfd_28 T_pureFD_8 T_pureFD_8 |
    C__'10814'__36 MAlonzo.Code.Untyped.T__'8866'_14 T_pureFD_8
                   T_pureFD_8 |
    C_translationfd_42 MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_16 |
    C_appfd_50 | C_appfd'8315''185'_58
-- VerifiedCompilation.UForceDelay.forceappdelay
d_forceappdelay_62 :: T_pureFD_8
d_forceappdelay_62
  = coe
      C__'10814'__36
      (coe
         MAlonzo.Code.Untyped.C__'183'__22
         (coe
            MAlonzo.Code.Untyped.C_ƛ_20
            (coe
               MAlonzo.Code.Untyped.C_force_24
               (coe
                  MAlonzo.Code.Untyped.C_delay_26
                  (coe
                     MAlonzo.Code.Untyped.C_'96'_18
                     (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))))
         (coe
            MAlonzo.Code.Untyped.C_'96'_18
            (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))
      (coe
         C_pushfd_28
         (coe
            C_translationfd_42
            (coe
               MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_match_106
               (coe
                  MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_delay_62
                  (coe
                     MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_match_106
                     (coe
                        MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_var_34)))))
         (coe
            C_translationfd_42
            (coe
               MAlonzo.Code.VerifiedCompilation.UntypedTranslation.du_reflexive_1756
               (coe
                  MAlonzo.Code.Untyped.C_'96'_18
                  (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
               (coe
                  MAlonzo.Code.VerifiedCompilation.Equality.du_DecEq'45'Maybe_122
                  (coe MAlonzo.Code.VerifiedCompilation.Equality.d_EmptyEq_128)))))
      (coe
         C_translationfd_42
         (coe
            MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_match_106
            (coe
               MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_app_50
               (coe
                  MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_match_106
                  (coe
                     MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_ƛ_40
                     (coe
                        MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_istranslation_100
                        (coe
                           C_forcedelay_18
                           (coe
                              C_translationfd_42
                              (coe
                                 MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_match_106
                                 (coe
                                    MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_var_34)))))))
               (coe
                  MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_match_106
                  (coe
                     MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_var_34)))))
-- VerifiedCompilation.UForceDelay.test4
d_test4_78 ::
  () ->
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> T_pureFD_8
d_test4_78 ~v0 v1 v2 v3 v4 = du_test4_78 v1 v2 v3 v4
du_test4_78 ::
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> T_pureFD_8
du_test4_78 v0 v1 v2 v3
  = coe
      C__'10814'__36
      (coe
         MAlonzo.Code.Untyped.C_force_24
         (coe
            MAlonzo.Code.Untyped.C__'183'__22
            (coe
               MAlonzo.Code.Untyped.C_ƛ_20
               (coe
                  MAlonzo.Code.Untyped.C__'183'__22
                  (coe
                     MAlonzo.Code.Untyped.C_ƛ_20
                     (coe MAlonzo.Code.Untyped.C_delay_26 (coe v1)))
                  (coe
                     MAlonzo.Code.Untyped.RenamingSubstitution.du_weaken_88 (coe v3))))
            (coe v2)))
      (coe
         C_translationfd_42
         (coe
            MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_match_106
            (coe
               MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_force_56
               (coe
                  MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_istranslation_100
                  (coe C_appfd_50)))))
      (coe
         C__'10814'__36
         (coe
            MAlonzo.Code.Untyped.C__'183'__22
            (coe
               MAlonzo.Code.Untyped.C_ƛ_20
               (coe
                  MAlonzo.Code.Untyped.C_force_24
                  (coe
                     MAlonzo.Code.Untyped.C__'183'__22
                     (coe
                        MAlonzo.Code.Untyped.C_ƛ_20
                        (coe MAlonzo.Code.Untyped.C_delay_26 (coe v1)))
                     (coe
                        MAlonzo.Code.Untyped.RenamingSubstitution.du_weaken_88 (coe v3)))))
            (coe v2))
         (coe
            C_pushfd_28
            (coe
               C_translationfd_42
               (coe
                  MAlonzo.Code.VerifiedCompilation.UntypedTranslation.du_reflexive_1756
                  (coe
                     MAlonzo.Code.Untyped.C__'183'__22
                     (coe
                        MAlonzo.Code.Untyped.C_ƛ_20
                        (coe MAlonzo.Code.Untyped.C_delay_26 (coe v1)))
                     (coe
                        MAlonzo.Code.Untyped.RenamingSubstitution.du_weaken_88 (coe v3)))
                  (coe
                     MAlonzo.Code.VerifiedCompilation.Equality.du_DecEq'45'Maybe_122
                     (coe v0))))
            (coe
               C_translationfd_42
               (coe
                  MAlonzo.Code.VerifiedCompilation.UntypedTranslation.du_reflexive_1756
                  (coe v2) (coe v0))))
         (coe
            C__'10814'__36
            (coe
               MAlonzo.Code.Untyped.C__'183'__22
               (coe
                  MAlonzo.Code.Untyped.C_ƛ_20
                  (coe
                     MAlonzo.Code.Untyped.C__'183'__22
                     (coe
                        MAlonzo.Code.Untyped.C_ƛ_20
                        (coe
                           MAlonzo.Code.Untyped.C_force_24
                           (coe MAlonzo.Code.Untyped.C_delay_26 (coe v1))))
                     (coe
                        MAlonzo.Code.Untyped.RenamingSubstitution.du_weaken_88 (coe v3))))
               (coe v2))
            (coe
               C_translationfd_42
               (coe
                  MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_match_106
                  (coe
                     MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_app_50
                     (coe
                        MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_match_106
                        (coe
                           MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_ƛ_40
                           (coe
                              MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_istranslation_100
                              (coe
                                 C_pushfd_28
                                 (coe
                                    C_translationfd_42
                                    (coe
                                       MAlonzo.Code.VerifiedCompilation.UntypedTranslation.du_reflexive_1756
                                       (coe MAlonzo.Code.Untyped.C_delay_26 (coe v1))
                                       (coe
                                          MAlonzo.Code.VerifiedCompilation.Equality.du_DecEq'45'Maybe_122
                                          (coe
                                             MAlonzo.Code.VerifiedCompilation.Equality.du_DecEq'45'Maybe_122
                                             (coe v0)))))
                                 (coe
                                    C_translationfd_42
                                    (coe
                                       MAlonzo.Code.VerifiedCompilation.UntypedTranslation.du_reflexive_1756
                                       (coe
                                          MAlonzo.Code.Untyped.RenamingSubstitution.du_weaken_88
                                          (coe v3))
                                       (coe
                                          MAlonzo.Code.VerifiedCompilation.Equality.du_DecEq'45'Maybe_122
                                          (coe v0))))))))
                     (coe
                        MAlonzo.Code.VerifiedCompilation.UntypedTranslation.du_reflexive_1756
                        (coe v2) (coe v0)))))
            (coe
               C__'10814'__36
               (coe
                  MAlonzo.Code.Untyped.C__'183'__22
                  (coe
                     MAlonzo.Code.Untyped.C_ƛ_20
                     (coe
                        MAlonzo.Code.Untyped.C__'183'__22
                        (coe MAlonzo.Code.Untyped.C_ƛ_20 (coe v1))
                        (coe
                           MAlonzo.Code.Untyped.RenamingSubstitution.du_weaken_88 (coe v3))))
                  (coe v2))
               (coe
                  C_translationfd_42
                  (coe
                     MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_match_106
                     (coe
                        MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_app_50
                        (coe
                           MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_match_106
                           (coe
                              MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_ƛ_40
                              (coe
                                 MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_match_106
                                 (coe
                                    MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_app_50
                                    (coe
                                       MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_match_106
                                       (coe
                                          MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_ƛ_40
                                          (coe
                                             MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_istranslation_100
                                             (coe
                                                C_forcedelay_18
                                                (coe
                                                   C_translationfd_42
                                                   (coe
                                                      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.du_reflexive_1756
                                                      (coe v1)
                                                      (coe
                                                         MAlonzo.Code.VerifiedCompilation.Equality.du_DecEq'45'Maybe_122
                                                         (coe
                                                            MAlonzo.Code.VerifiedCompilation.Equality.du_DecEq'45'Maybe_122
                                                            (coe v0)))))))))
                                    (coe
                                       MAlonzo.Code.VerifiedCompilation.UntypedTranslation.du_reflexive_1756
                                       (coe
                                          MAlonzo.Code.Untyped.RenamingSubstitution.du_weaken_88
                                          (coe v3))
                                       (coe
                                          MAlonzo.Code.VerifiedCompilation.Equality.du_DecEq'45'Maybe_122
                                          (coe v0)))))))
                        (coe
                           MAlonzo.Code.VerifiedCompilation.UntypedTranslation.du_reflexive_1756
                           (coe v2) (coe v0)))))
               (coe C_appfd'8315''185'_58))))
-- VerifiedCompilation.UForceDelay.FD
d_FD_84 a0 a1 a2 a3 a4 a5 = ()
data T_FD_84
  = C_forcefd_98 T_FD_84 | C_delayfd_108 T_FD_84 |
    C_lastdelay_118 Integer Integer
                    MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_16 |
    C_multiappliedfd_132 MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_16
                         T_FD_84 |
    C_multiabstractfd_142 T_FD_84
-- VerifiedCompilation.UForceDelay.ForceDelay
d_ForceDelay_160 ::
  () ->
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> ()
d_ForceDelay_160 = erased
-- VerifiedCompilation.UForceDelay.t
d_t_162 :: MAlonzo.Code.Untyped.T__'8866'_14
d_t_162
  = coe
      MAlonzo.Code.Untyped.C_force_24
      (coe
         MAlonzo.Code.Untyped.C__'183'__22
         (coe
            MAlonzo.Code.Untyped.C__'183'__22
            (coe
               MAlonzo.Code.Untyped.C_ƛ_20
               (coe
                  MAlonzo.Code.Untyped.C_ƛ_20
                  (coe
                     MAlonzo.Code.Untyped.C_delay_26
                     (coe MAlonzo.Code.Untyped.C_error_46))))
            (coe MAlonzo.Code.Untyped.C_error_46))
         (coe MAlonzo.Code.Untyped.C_error_46))
-- VerifiedCompilation.UForceDelay.t'
d_t''_164 :: MAlonzo.Code.Untyped.T__'8866'_14
d_t''_164
  = coe
      MAlonzo.Code.Untyped.C__'183'__22
      (coe
         MAlonzo.Code.Untyped.C__'183'__22
         (coe
            MAlonzo.Code.Untyped.C_ƛ_20
            (coe
               MAlonzo.Code.Untyped.C_ƛ_20 (coe MAlonzo.Code.Untyped.C_error_46)))
         (coe MAlonzo.Code.Untyped.C_error_46))
      (coe MAlonzo.Code.Untyped.C_error_46)
-- VerifiedCompilation.UForceDelay.test-ffdd
d_test'45'ffdd_166 :: T_FD_84
d_test'45'ffdd_166
  = coe
      C_forcefd_98
      (coe
         C_forcefd_98
         (coe
            C_delayfd_108
            (coe
               C_lastdelay_118 (0 :: Integer) (0 :: Integer)
               (coe
                  MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_match_106
                  (coe
                     MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_error_90)))))
-- VerifiedCompilation.UForceDelay.isForceDelay?
d_isForceDelay'63'_176 ::
  () ->
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_26
d_isForceDelay'63'_176 ~v0 v1 = du_isForceDelay'63'_176 v1
du_isForceDelay'63'_176 ::
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_26
du_isForceDelay'63'_176 v0
  = coe
      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.du_translation'63'_178
      erased (coe v0)
      (coe MAlonzo.Code.VerifiedCompilation.Certificate.C_forceDelayT_8)
      (coe
         (\ v1 v2 ->
            coe
              du_isFD'63'_186 (coe v2) (coe (0 :: Integer))
              (coe (0 :: Integer))))
-- VerifiedCompilation.UForceDelay.isFD?
d_isFD'63'_186 ::
  () ->
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_26
d_isFD'63'_186 ~v0 v1 v2 v3 v4 v5 = du_isFD'63'_186 v1 v2 v3 v4 v5
du_isFD'63'_186 ::
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_26
du_isFD'63'_186 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isForce'63'_284
              erased
              (\ v5 v6 ->
                 coe
                   MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)
              (coe v3) in
    coe
      (case coe v5 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
           -> if coe v6
                then case coe v7 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v8
                         -> case coe v8 of
                              MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isforce_276 v10
                                -> case coe v3 of
                                     MAlonzo.Code.Untyped.C_force_24 v11
                                       -> coe
                                            seq (coe v10)
                                            (let v12
                                                   = coe
                                                       MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isApp'63'_166
                                                       erased
                                                       (\ v12 v13 ->
                                                          coe
                                                            MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)
                                                       (\ v12 v13 ->
                                                          coe
                                                            MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)
                                                       (coe v11) in
                                             coe
                                               (case coe v12 of
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                                    -> if coe v13
                                                         then case coe v14 of
                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v15
                                                                  -> case coe v15 of
                                                                       MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isapp_154 v18 v19
                                                                         -> case coe v11 of
                                                                              MAlonzo.Code.Untyped.C__'183'__22 v20 v21
                                                                                -> coe
                                                                                     seq (coe v18)
                                                                                     (coe
                                                                                        seq
                                                                                        (coe v19)
                                                                                        (let v22
                                                                                               = coe
                                                                                                   MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isApp'63'_166
                                                                                                   erased
                                                                                                   (\ v22
                                                                                                      v23 ->
                                                                                                      coe
                                                                                                        MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)
                                                                                                   (\ v22
                                                                                                      v23 ->
                                                                                                      coe
                                                                                                        MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)
                                                                                                   (coe
                                                                                                      v4) in
                                                                                         coe
                                                                                           (case coe
                                                                                                   v22 of
                                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v23 v24
                                                                                                -> if coe
                                                                                                        v23
                                                                                                     then case coe
                                                                                                                 v24 of
                                                                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v25
                                                                                                              -> case coe
                                                                                                                        v25 of
                                                                                                                   MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isapp_154 v28 v29
                                                                                                                     -> case coe
                                                                                                                               v4 of
                                                                                                                          MAlonzo.Code.Untyped.C__'183'__22 v30 v31
                                                                                                                            -> coe
                                                                                                                                 seq
                                                                                                                                 (coe
                                                                                                                                    v28)
                                                                                                                                 (coe
                                                                                                                                    seq
                                                                                                                                    (coe
                                                                                                                                       v29)
                                                                                                                                    (let v32
                                                                                                                                           = coe
                                                                                                                                               du_isFD'63'_186
                                                                                                                                               (coe
                                                                                                                                                  v0)
                                                                                                                                               (coe
                                                                                                                                                  v1)
                                                                                                                                               (coe
                                                                                                                                                  addInt
                                                                                                                                                  (coe
                                                                                                                                                     (1 ::
                                                                                                                                                        Integer))
                                                                                                                                                  (coe
                                                                                                                                                     v2))
                                                                                                                                               (coe
                                                                                                                                                  MAlonzo.Code.Untyped.C_force_24
                                                                                                                                                  (coe
                                                                                                                                                     v20))
                                                                                                                                               (coe
                                                                                                                                                  v30) in
                                                                                                                                     coe
                                                                                                                                       (case coe
                                                                                                                                               v32 of
                                                                                                                                          MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32 v33
                                                                                                                                            -> let v34
                                                                                                                                                     = coe
                                                                                                                                                         du_isForceDelay'63'_176
                                                                                                                                                         v0
                                                                                                                                                         v21
                                                                                                                                                         v31 in
                                                                                                                                               coe
                                                                                                                                                 (case coe
                                                                                                                                                         v34 of
                                                                                                                                                    MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32 v35
                                                                                                                                                      -> coe
                                                                                                                                                           MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32
                                                                                                                                                           (coe
                                                                                                                                                              C_multiappliedfd_132
                                                                                                                                                              v35
                                                                                                                                                              v33)
                                                                                                                                                    MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40 v38 v39 v40
                                                                                                                                                      -> coe
                                                                                                                                                           MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40
                                                                                                                                                           v38
                                                                                                                                                           v39
                                                                                                                                                           v40
                                                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                          MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40 v36 v37 v38
                                                                                                                                            -> coe
                                                                                                                                                 MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40
                                                                                                                                                 v36
                                                                                                                                                 v37
                                                                                                                                                 v38
                                                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError)))
                                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                     else coe
                                                                                                            seq
                                                                                                            (coe
                                                                                                               v24)
                                                                                                            (coe
                                                                                                               MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.VerifiedCompilation.Certificate.C_forceDelayT_8)
                                                                                                               v3
                                                                                                               v4)
                                                                                              _ -> MAlonzo.RTE.mazUnreachableError)))
                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         else coe
                                                                seq (coe v14)
                                                                (let v15
                                                                       = coe
                                                                           MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isLambda'63'_70
                                                                           (\ v15 v16 ->
                                                                              coe
                                                                                MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)
                                                                           (coe v11) in
                                                                 coe
                                                                   (case coe v15 of
                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                        -> if coe v16
                                                                             then case coe v17 of
                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v18
                                                                                      -> case coe
                                                                                                v18 of
                                                                                           MAlonzo.Code.VerifiedCompilation.UntypedViews.C_islambda_62 v20
                                                                                             -> case coe
                                                                                                       v11 of
                                                                                                  MAlonzo.Code.Untyped.C_ƛ_20 v21
                                                                                                    -> coe
                                                                                                         seq
                                                                                                         (coe
                                                                                                            v20)
                                                                                                         (case coe
                                                                                                                 v2 of
                                                                                                            0 -> coe
                                                                                                                   MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40
                                                                                                                   (coe
                                                                                                                      MAlonzo.Code.VerifiedCompilation.Certificate.C_forceDelayT_8)
                                                                                                                   v3
                                                                                                                   v4
                                                                                                            _ -> let v22
                                                                                                                       = subInt
                                                                                                                           (coe
                                                                                                                              v2)
                                                                                                                           (coe
                                                                                                                              (1 ::
                                                                                                                                 Integer)) in
                                                                                                                 coe
                                                                                                                   (let v23
                                                                                                                          = coe
                                                                                                                              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isLambda'63'_70
                                                                                                                              (\ v23
                                                                                                                                 v24 ->
                                                                                                                                 coe
                                                                                                                                   MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)
                                                                                                                              (coe
                                                                                                                                 v4) in
                                                                                                                    coe
                                                                                                                      (case coe
                                                                                                                              v23 of
                                                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v24 v25
                                                                                                                           -> if coe
                                                                                                                                   v24
                                                                                                                                then case coe
                                                                                                                                            v25 of
                                                                                                                                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v26
                                                                                                                                         -> case coe
                                                                                                                                                   v26 of
                                                                                                                                              MAlonzo.Code.VerifiedCompilation.UntypedViews.C_islambda_62 v28
                                                                                                                                                -> case coe
                                                                                                                                                          v4 of
                                                                                                                                                     MAlonzo.Code.Untyped.C_ƛ_20 v29
                                                                                                                                                       -> coe
                                                                                                                                                            seq
                                                                                                                                                            (coe
                                                                                                                                                               v28)
                                                                                                                                                            (let v30
                                                                                                                                                                   = coe
                                                                                                                                                                       du_isFD'63'_186
                                                                                                                                                                       (coe
                                                                                                                                                                          MAlonzo.Code.VerifiedCompilation.Equality.du_DecEq'45'Maybe_122
                                                                                                                                                                          (coe
                                                                                                                                                                             v0))
                                                                                                                                                                       (coe
                                                                                                                                                                          v1)
                                                                                                                                                                       (coe
                                                                                                                                                                          v22)
                                                                                                                                                                       (coe
                                                                                                                                                                          MAlonzo.Code.Untyped.C_force_24
                                                                                                                                                                          (coe
                                                                                                                                                                             v21))
                                                                                                                                                                       (coe
                                                                                                                                                                          v29) in
                                                                                                                                                             coe
                                                                                                                                                               (case coe
                                                                                                                                                                       v30 of
                                                                                                                                                                  MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32 v31
                                                                                                                                                                    -> coe
                                                                                                                                                                         MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32
                                                                                                                                                                         (coe
                                                                                                                                                                            C_multiabstractfd_142
                                                                                                                                                                            v31)
                                                                                                                                                                  MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40 v34 v35 v36
                                                                                                                                                                    -> coe
                                                                                                                                                                         MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40
                                                                                                                                                                         v34
                                                                                                                                                                         v35
                                                                                                                                                                         v36
                                                                                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                else coe
                                                                                                                                       seq
                                                                                                                                       (coe
                                                                                                                                          v25)
                                                                                                                                       (coe
                                                                                                                                          MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40
                                                                                                                                          (coe
                                                                                                                                             MAlonzo.Code.VerifiedCompilation.Certificate.C_forceDelayT_8)
                                                                                                                                          v3
                                                                                                                                          v4)
                                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError)))
                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                             else coe
                                                                                    seq (coe v17)
                                                                                    (let v18
                                                                                           = coe
                                                                                               du_isFD'63'_186
                                                                                               (coe
                                                                                                  v0)
                                                                                               (coe
                                                                                                  addInt
                                                                                                  (coe
                                                                                                     (1 ::
                                                                                                        Integer))
                                                                                                  (coe
                                                                                                     v1))
                                                                                               (coe
                                                                                                  v2)
                                                                                               (coe
                                                                                                  v11)
                                                                                               (coe
                                                                                                  v4) in
                                                                                     coe
                                                                                       (case coe
                                                                                               v18 of
                                                                                          MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32 v19
                                                                                            -> coe
                                                                                                 MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32
                                                                                                 (coe
                                                                                                    C_forcefd_98
                                                                                                    v19)
                                                                                          MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40 v22 v23 v24
                                                                                            -> coe
                                                                                                 MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40
                                                                                                 v22
                                                                                                 v23
                                                                                                 v24
                                                                                          _ -> MAlonzo.RTE.mazUnreachableError))
                                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v7)
                       (case coe v1 of
                          0 -> coe
                                 MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40
                                 (coe MAlonzo.Code.VerifiedCompilation.Certificate.C_forceDelayT_8)
                                 v3 v4
                          _ -> let v8 = subInt (coe v1) (coe (1 :: Integer)) in
                               coe
                                 (let v9
                                        = coe
                                            MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isDelay'63'_370
                                            erased
                                            (\ v9 v10 ->
                                               coe
                                                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)
                                            (coe v3) in
                                  coe
                                    (case coe v9 of
                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                         -> if coe v10
                                              then case coe v11 of
                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v12
                                                       -> case coe v12 of
                                                            MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isdelay_362 v14
                                                              -> case coe v3 of
                                                                   MAlonzo.Code.Untyped.C_delay_26 v15
                                                                     -> coe
                                                                          seq (coe v14)
                                                                          (let v16
                                                                                 = coe
                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__76
                                                                                     (coe
                                                                                        MAlonzo.Code.Data.Nat.Properties.d__'8799'__2688
                                                                                        (coe v8)
                                                                                        (coe
                                                                                           (0 ::
                                                                                              Integer)))
                                                                                     (coe
                                                                                        MAlonzo.Code.Data.Nat.Properties.d__'8799'__2688
                                                                                        (coe v2)
                                                                                        (coe
                                                                                           (0 ::
                                                                                              Integer))) in
                                                                           coe
                                                                             (case coe v16 of
                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                                  -> if coe v17
                                                                                       then case coe
                                                                                                   v18 of
                                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v19
                                                                                                -> coe
                                                                                                     seq
                                                                                                     (coe
                                                                                                        v19)
                                                                                                     (let v20
                                                                                                            = coe
                                                                                                                du_isForceDelay'63'_176
                                                                                                                v0
                                                                                                                v15
                                                                                                                v4 in
                                                                                                      coe
                                                                                                        (case coe
                                                                                                                v20 of
                                                                                                           MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32 v21
                                                                                                             -> coe
                                                                                                                  MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32
                                                                                                                  (coe
                                                                                                                     C_lastdelay_118
                                                                                                                     (0 ::
                                                                                                                        Integer)
                                                                                                                     (0 ::
                                                                                                                        Integer)
                                                                                                                     v21)
                                                                                                           MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40 v24 v25 v26
                                                                                                             -> coe
                                                                                                                  MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40
                                                                                                                  v24
                                                                                                                  v25
                                                                                                                  v26
                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                       else coe
                                                                                              seq
                                                                                              (coe
                                                                                                 v18)
                                                                                              (let v19
                                                                                                     = coe
                                                                                                         du_isFD'63'_186
                                                                                                         (coe
                                                                                                            v0)
                                                                                                         (coe
                                                                                                            v8)
                                                                                                         (coe
                                                                                                            v2)
                                                                                                         (coe
                                                                                                            v15)
                                                                                                         (coe
                                                                                                            v4) in
                                                                                               coe
                                                                                                 (case coe
                                                                                                         v19 of
                                                                                                    MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32 v20
                                                                                                      -> coe
                                                                                                           MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32
                                                                                                           (coe
                                                                                                              C_delayfd_108
                                                                                                              v20)
                                                                                                    MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40 v23 v24 v25
                                                                                                      -> coe
                                                                                                           MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40
                                                                                                           v23
                                                                                                           v24
                                                                                                           v25
                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                _ -> MAlonzo.RTE.mazUnreachableError))
                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              else coe
                                                     seq (coe v11)
                                                     (coe
                                                        MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40
                                                        (coe
                                                           MAlonzo.Code.VerifiedCompilation.Certificate.C_forceDelayT_8)
                                                        v3 v4)
                                       _ -> MAlonzo.RTE.mazUnreachableError)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.UForceDelay..extendedlambda0
d_'46'extendedlambda0_208 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isForce_268 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  T_FD_84 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda0_208 = erased
-- VerifiedCompilation.UForceDelay..extendedlambda1
d_'46'extendedlambda1_246 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isDelay_354 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isForce_268 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  T_FD_84 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda1_246 = erased
-- VerifiedCompilation.UForceDelay..extendedlambda2
d_'46'extendedlambda2_322 ::
  Integer ->
  Integer ->
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (T_FD_84 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isForce_268 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_FD_84 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda2_322 = erased
-- VerifiedCompilation.UForceDelay..extendedlambda3
d_'46'extendedlambda3_384 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isForce_268 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_FD_84 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda3_384 = erased
-- VerifiedCompilation.UForceDelay..extendedlambda4
d_'46'extendedlambda4_456 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isApp_142 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  Integer ->
  Integer -> T_FD_84 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda4_456 = erased
-- VerifiedCompilation.UForceDelay..extendedlambda5
d_'46'extendedlambda5_510 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  Integer ->
  Integer ->
  (T_FD_84 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  T_FD_84 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda5_510 = erased
-- VerifiedCompilation.UForceDelay..extendedlambda6
d_'46'extendedlambda6_568 ::
  () ->
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Integer ->
  Integer ->
  T_FD_84 -> T_FD_84 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda6_568 = erased
-- VerifiedCompilation.UForceDelay..extendedlambda7
d_'46'extendedlambda7_646 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isLambda_54 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isApp_142 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  Integer ->
  Integer -> T_FD_84 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda7_646 = erased
-- VerifiedCompilation.UForceDelay..extendedlambda8
d_'46'extendedlambda8_694 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  Integer ->
  Integer ->
  (T_FD_84 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isApp_142 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_FD_84 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda8_694 = erased
-- VerifiedCompilation.UForceDelay..extendedlambda9
d_'46'extendedlambda9_728 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isApp_142 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  T_FD_84 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda9_728 = erased
-- VerifiedCompilation.UForceDelay..extendedlambda10
d_'46'extendedlambda10_786 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (T_FD_84 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isLambda_54 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isApp_142 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_FD_84 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda10_786 = erased
