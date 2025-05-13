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
-- VerifiedCompilation.UForceDelay.Zipper
d_Zipper_84 a0 = ()
data T_Zipper_84
  = C_'9633'_88 | C_force_90 T_Zipper_84 |
    C__'183'__92 T_Zipper_84 MAlonzo.Code.Untyped.T__'8866'_14
-- VerifiedCompilation.UForceDelay.zipwk
d_zipwk_94 :: () -> T_Zipper_84 -> T_Zipper_84
d_zipwk_94 ~v0 v1 = du_zipwk_94 v1
du_zipwk_94 :: T_Zipper_84 -> T_Zipper_84
du_zipwk_94 v0
  = case coe v0 of
      C_'9633'_88 -> coe v0
      C_force_90 v1 -> coe C_force_90 (coe du_zipwk_94 (coe v1))
      C__'183'__92 v1 v2
        -> coe
             C__'183'__92 (coe du_zipwk_94 (coe v1))
             (coe
                MAlonzo.Code.Untyped.RenamingSubstitution.du_weaken_88 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.UForceDelay.FD
d_FD_116 a0 a1 a2 a3 a4 = ()
data T_FD_116
  = C_force_122 T_FD_116 | C_delay_124 T_FD_116 |
    C_app_126 T_FD_116
              MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_16 |
    C_abs_128 T_FD_116 |
    C_last'45'delay_130 MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_16 |
    C_last'45'abs_132 MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_16
-- VerifiedCompilation.UForceDelay.ForceDelay
d_ForceDelay_150 ::
  () ->
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> ()
d_ForceDelay_150 = erased
-- VerifiedCompilation.UForceDelay.t
d_t_152 :: MAlonzo.Code.Untyped.T__'8866'_14
d_t_152
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
d_t''_154 :: MAlonzo.Code.Untyped.T__'8866'_14
d_t''_154
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
d_test'45'ffdd_156 :: T_FD_116
d_test'45'ffdd_156
  = coe
      C_force_122
      (coe
         C_force_122
         (coe
            C_delay_124
            (coe
               C_last'45'delay_130
               (coe
                  MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_match_106
                  (coe
                     MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_error_90)))))
-- VerifiedCompilation.UForceDelay.One
d_One_162
  = error
      "MAlonzo Runtime Error: postulate evaluated: VerifiedCompilation.UForceDelay.One"
-- VerifiedCompilation.UForceDelay.Two
d_Two_164
  = error
      "MAlonzo Runtime Error: postulate evaluated: VerifiedCompilation.UForceDelay.Two"
-- VerifiedCompilation.UForceDelay.Three
d_Three_166
  = error
      "MAlonzo Runtime Error: postulate evaluated: VerifiedCompilation.UForceDelay.Three"
-- VerifiedCompilation.UForceDelay.forceDelaySimpleBefore
d_forceDelaySimpleBefore_168 :: MAlonzo.Code.Untyped.T__'8866'_14
d_forceDelaySimpleBefore_168
  = coe
      MAlonzo.Code.Untyped.C__'183'__22
      (coe
         MAlonzo.Code.Untyped.C_force_24
         (coe
            MAlonzo.Code.Untyped.C__'183'__22
            (coe
               MAlonzo.Code.Untyped.C_force_24
               (coe
                  MAlonzo.Code.Untyped.C__'183'__22
                  (coe
                     MAlonzo.Code.Untyped.C_force_24
                     (coe
                        MAlonzo.Code.Untyped.C_delay_26
                        (coe
                           MAlonzo.Code.Untyped.C_ƛ_20
                           (coe
                              MAlonzo.Code.Untyped.C_delay_26
                              (coe
                                 MAlonzo.Code.Untyped.C_ƛ_20
                                 (coe
                                    MAlonzo.Code.Untyped.C_delay_26
                                    (coe
                                       MAlonzo.Code.Untyped.C_ƛ_20
                                       (coe
                                          MAlonzo.Code.Untyped.C_'96'_18
                                          (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))))))))
                  (coe MAlonzo.Code.Untyped.C_con_28 (coe d_One_162))))
            (coe MAlonzo.Code.Untyped.C_con_28 (coe d_Two_164))))
      (coe MAlonzo.Code.Untyped.C_con_28 (coe d_Three_166))
-- VerifiedCompilation.UForceDelay.forceDelaySimpleAfter
d_forceDelaySimpleAfter_170 :: MAlonzo.Code.Untyped.T__'8866'_14
d_forceDelaySimpleAfter_170
  = coe
      MAlonzo.Code.Untyped.C__'183'__22
      (coe
         MAlonzo.Code.Untyped.C__'183'__22
         (coe
            MAlonzo.Code.Untyped.C__'183'__22
            (coe
               MAlonzo.Code.Untyped.C_ƛ_20
               (coe
                  MAlonzo.Code.Untyped.C_ƛ_20
                  (coe
                     MAlonzo.Code.Untyped.C_ƛ_20
                     (coe
                        MAlonzo.Code.Untyped.C_'96'_18
                        (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))))
            (coe MAlonzo.Code.Untyped.C_con_28 (coe d_One_162)))
         (coe MAlonzo.Code.Untyped.C_con_28 (coe d_Two_164)))
      (coe MAlonzo.Code.Untyped.C_con_28 (coe d_Three_166))
-- VerifiedCompilation.UForceDelay.forceDelaySimple
d_forceDelaySimple_172 :: T_FD_116
d_forceDelaySimple_172
  = coe
      C_app_126
      (coe
         C_force_122
         (coe
            C_app_126
            (coe
               C_force_122
               (coe
                  C_app_126
                  (coe
                     C_force_122
                     (coe
                        C_delay_124
                        (coe
                           C_abs_128
                           (coe
                              C_delay_124
                              (coe
                                 C_abs_128
                                 (coe
                                    C_delay_124
                                    (coe
                                       C_last'45'abs_132
                                       (coe
                                          MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_match_106
                                          (coe
                                             MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_var_34)))))))))
                  (coe
                     MAlonzo.Code.VerifiedCompilation.UntypedTranslation.du_reflexive_1756
                     (coe MAlonzo.Code.Untyped.C_con_28 (coe d_One_162))
                     (coe MAlonzo.Code.VerifiedCompilation.Equality.d_EmptyEq_128))))
            (coe
               MAlonzo.Code.VerifiedCompilation.UntypedTranslation.du_reflexive_1756
               (coe MAlonzo.Code.Untyped.C_con_28 (coe d_Two_164))
               (coe MAlonzo.Code.VerifiedCompilation.Equality.d_EmptyEq_128))))
      (coe
         MAlonzo.Code.VerifiedCompilation.UntypedTranslation.du_reflexive_1756
         (coe MAlonzo.Code.Untyped.C_con_28 (coe d_Three_166))
         (coe MAlonzo.Code.VerifiedCompilation.Equality.d_EmptyEq_128))
-- VerifiedCompilation.UForceDelay.isForceDelay?
d_isForceDelay'63'_178 ::
  () ->
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_26
d_isForceDelay'63'_178 ~v0 v1 = du_isForceDelay'63'_178 v1
du_isForceDelay'63'_178 ::
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_26
du_isForceDelay'63'_178 v0
  = coe
      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.du_translation'63'_178
      erased (coe v0)
      (coe MAlonzo.Code.VerifiedCompilation.Certificate.C_forceDelayT_8)
      (coe (\ v1 v2 -> coe du_isFD'63'_186 (coe v2) (coe C_'9633'_88)))
-- VerifiedCompilation.UForceDelay.isFD?
d_isFD'63'_186 ::
  () ->
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  T_Zipper_84 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_26
d_isFD'63'_186 ~v0 v1 v2 v3 v4 = du_isFD'63'_186 v1 v2 v3 v4
du_isFD'63'_186 ::
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  T_Zipper_84 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_26
du_isFD'63'_186 v0 v1 v2 v3
  = case coe v1 of
      C_'9633'_88
        -> let v4
                 = coe
                     MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isForce'63'_284
                     erased
                     (\ v4 v5 ->
                        coe
                          MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)
                     (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                  -> if coe v5
                       then case coe v6 of
                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v7
                                -> case coe v7 of
                                     MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isforce_276 v9
                                       -> case coe v2 of
                                            MAlonzo.Code.Untyped.C_force_24 v10
                                              -> coe
                                                   seq (coe v9)
                                                   (let v11
                                                          = coe
                                                              du_isFD'63'_186 (coe v0)
                                                              (coe C_force_90 (coe v1)) (coe v10)
                                                              (coe v3) in
                                                    coe
                                                      (case coe v11 of
                                                         MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32 v12
                                                           -> coe
                                                                MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32
                                                                (coe C_force_122 v12)
                                                         MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40 v15 v16 v17
                                                           -> coe
                                                                MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40
                                                                v15 v16 v17
                                                         _ -> MAlonzo.RTE.mazUnreachableError))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       else coe
                              seq (coe v6)
                              (let v7
                                     = coe
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__76
                                         (coe
                                            MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isApp'63'_166
                                            erased
                                            (\ v7 v8 ->
                                               coe
                                                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)
                                            (\ v7 v8 ->
                                               coe
                                                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)
                                            (coe v2))
                                         (coe
                                            MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isApp'63'_166
                                            erased
                                            (\ v7 v8 ->
                                               coe
                                                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)
                                            (\ v7 v8 ->
                                               coe
                                                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)
                                            (coe v3)) in
                               coe
                                 (case coe v7 of
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                      -> if coe v8
                                           then case coe v9 of
                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v10
                                                    -> case coe v10 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                           -> case coe v11 of
                                                                MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isapp_154 v15 v16
                                                                  -> case coe v2 of
                                                                       MAlonzo.Code.Untyped.C__'183'__22 v17 v18
                                                                         -> coe
                                                                              seq (coe v15)
                                                                              (coe
                                                                                 seq (coe v16)
                                                                                 (case coe v12 of
                                                                                    MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isapp_154 v21 v22
                                                                                      -> case coe
                                                                                                v3 of
                                                                                           MAlonzo.Code.Untyped.C__'183'__22 v23 v24
                                                                                             -> coe
                                                                                                  seq
                                                                                                  (coe
                                                                                                     v21)
                                                                                                  (coe
                                                                                                     seq
                                                                                                     (coe
                                                                                                        v22)
                                                                                                     (let v25
                                                                                                            = coe
                                                                                                                du_isForceDelay'63'_178
                                                                                                                v0
                                                                                                                v18
                                                                                                                v24 in
                                                                                                      coe
                                                                                                        (case coe
                                                                                                                v25 of
                                                                                                           MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32 v26
                                                                                                             -> let v27
                                                                                                                      = coe
                                                                                                                          du_isFD'63'_186
                                                                                                                          (coe
                                                                                                                             v0)
                                                                                                                          (coe
                                                                                                                             C__'183'__92
                                                                                                                             (coe
                                                                                                                                v1)
                                                                                                                             (coe
                                                                                                                                v24))
                                                                                                                          (coe
                                                                                                                             v17)
                                                                                                                          (coe
                                                                                                                             v23) in
                                                                                                                coe
                                                                                                                  (case coe
                                                                                                                          v27 of
                                                                                                                     MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32 v28
                                                                                                                       -> coe
                                                                                                                            MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32
                                                                                                                            (coe
                                                                                                                               C_app_126
                                                                                                                               v28
                                                                                                                               v26)
                                                                                                                     MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40 v31 v32 v33
                                                                                                                       -> coe
                                                                                                                            MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40
                                                                                                                            v31
                                                                                                                            v32
                                                                                                                            v33
                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                           MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40 v29 v30 v31
                                                                                                             -> coe
                                                                                                                  MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40
                                                                                                                  v29
                                                                                                                  v30
                                                                                                                  v31
                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError)))
                                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError))
                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           else coe
                                                  seq (coe v9)
                                                  (coe
                                                     MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40
                                                     (coe
                                                        MAlonzo.Code.VerifiedCompilation.Certificate.C_forceDelayT_8)
                                                     v2 v3)
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_force_90 v4
        -> let v5
                 = coe
                     MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isDelay'63'_370
                     erased
                     (\ v5 v6 ->
                        coe
                          MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)
                     (coe v2) in
           coe
             (case coe v5 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                  -> if coe v6
                       then case coe v7 of
                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v8
                                -> case coe v8 of
                                     MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isdelay_362 v10
                                       -> case coe v2 of
                                            MAlonzo.Code.Untyped.C_delay_26 v11
                                              -> coe
                                                   seq (coe v10)
                                                   (let v12
                                                          = coe
                                                              du_isFD'63'_186 (coe v0) (coe v4)
                                                              (coe v11) (coe v3) in
                                                    coe
                                                      (case coe v12 of
                                                         MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32 v13
                                                           -> coe
                                                                MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32
                                                                (coe C_delay_124 v13)
                                                         MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40 v16 v17 v18
                                                           -> case coe v4 of
                                                                C_'9633'_88
                                                                  -> let v19
                                                                           = coe
                                                                               du_isForceDelay'63'_178
                                                                               v0 v11 v3 in
                                                                     coe
                                                                       (case coe v19 of
                                                                          MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32 v20
                                                                            -> coe
                                                                                 MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32
                                                                                 (coe
                                                                                    C_last'45'delay_130
                                                                                    v20)
                                                                          MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40 v23 v24 v25
                                                                            -> coe
                                                                                 MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40
                                                                                 (coe
                                                                                    MAlonzo.Code.VerifiedCompilation.Certificate.C_forceDelayT_8)
                                                                                 v2 v3
                                                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                                                C_force_90 v19
                                                                  -> coe
                                                                       MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40
                                                                       v16 v17 v18
                                                                C__'183'__92 v19 v20
                                                                  -> coe
                                                                       MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40
                                                                       v16 v17 v18
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         _ -> MAlonzo.RTE.mazUnreachableError))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       else coe
                              seq (coe v7)
                              (let v8
                                     = coe
                                         MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isForce'63'_284
                                         erased
                                         (\ v8 v9 ->
                                            coe
                                              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)
                                         (coe v2) in
                               coe
                                 (case coe v8 of
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                      -> if coe v9
                                           then case coe v10 of
                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v11
                                                    -> case coe v11 of
                                                         MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isforce_276 v13
                                                           -> case coe v2 of
                                                                MAlonzo.Code.Untyped.C_force_24 v14
                                                                  -> coe
                                                                       seq (coe v13)
                                                                       (let v15
                                                                              = coe
                                                                                  du_isFD'63'_186
                                                                                  (coe v0)
                                                                                  (coe
                                                                                     C_force_90
                                                                                     (coe v1))
                                                                                  (coe v14)
                                                                                  (coe v3) in
                                                                        coe
                                                                          (case coe v15 of
                                                                             MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32 v16
                                                                               -> coe
                                                                                    MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32
                                                                                    (coe
                                                                                       C_force_122
                                                                                       v16)
                                                                             MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40 v19 v20 v21
                                                                               -> coe
                                                                                    MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40
                                                                                    v19 v20 v21
                                                                             _ -> MAlonzo.RTE.mazUnreachableError))
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           else coe
                                                  seq (coe v10)
                                                  (let v11
                                                         = coe
                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__76
                                                             (coe
                                                                MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isApp'63'_166
                                                                erased
                                                                (\ v11 v12 ->
                                                                   coe
                                                                     MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)
                                                                (\ v11 v12 ->
                                                                   coe
                                                                     MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)
                                                                (coe v2))
                                                             (coe
                                                                MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isApp'63'_166
                                                                erased
                                                                (\ v11 v12 ->
                                                                   coe
                                                                     MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)
                                                                (\ v11 v12 ->
                                                                   coe
                                                                     MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)
                                                                (coe v3)) in
                                                   coe
                                                     (case coe v11 of
                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                                          -> if coe v12
                                                               then case coe v13 of
                                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v14
                                                                        -> case coe v14 of
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                               -> case coe v15 of
                                                                                    MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isapp_154 v19 v20
                                                                                      -> case coe
                                                                                                v2 of
                                                                                           MAlonzo.Code.Untyped.C__'183'__22 v21 v22
                                                                                             -> coe
                                                                                                  seq
                                                                                                  (coe
                                                                                                     v19)
                                                                                                  (coe
                                                                                                     seq
                                                                                                     (coe
                                                                                                        v20)
                                                                                                     (case coe
                                                                                                             v16 of
                                                                                                        MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isapp_154 v25 v26
                                                                                                          -> case coe
                                                                                                                    v3 of
                                                                                                               MAlonzo.Code.Untyped.C__'183'__22 v27 v28
                                                                                                                 -> coe
                                                                                                                      seq
                                                                                                                      (coe
                                                                                                                         v25)
                                                                                                                      (coe
                                                                                                                         seq
                                                                                                                         (coe
                                                                                                                            v26)
                                                                                                                         (let v29
                                                                                                                                = coe
                                                                                                                                    du_isForceDelay'63'_178
                                                                                                                                    v0
                                                                                                                                    v22
                                                                                                                                    v28 in
                                                                                                                          coe
                                                                                                                            (case coe
                                                                                                                                    v29 of
                                                                                                                               MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32 v30
                                                                                                                                 -> let v31
                                                                                                                                          = coe
                                                                                                                                              du_isFD'63'_186
                                                                                                                                              (coe
                                                                                                                                                 v0)
                                                                                                                                              (coe
                                                                                                                                                 C__'183'__92
                                                                                                                                                 (coe
                                                                                                                                                    v1)
                                                                                                                                                 (coe
                                                                                                                                                    v28))
                                                                                                                                              (coe
                                                                                                                                                 v21)
                                                                                                                                              (coe
                                                                                                                                                 v27) in
                                                                                                                                    coe
                                                                                                                                      (case coe
                                                                                                                                              v31 of
                                                                                                                                         MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32 v32
                                                                                                                                           -> coe
                                                                                                                                                MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32
                                                                                                                                                (coe
                                                                                                                                                   C_app_126
                                                                                                                                                   v32
                                                                                                                                                   v30)
                                                                                                                                         MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40 v35 v36 v37
                                                                                                                                           -> coe
                                                                                                                                                MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40
                                                                                                                                                v35
                                                                                                                                                v36
                                                                                                                                                v37
                                                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                               MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40 v33 v34 v35
                                                                                                                                 -> coe
                                                                                                                                      MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40
                                                                                                                                      v33
                                                                                                                                      v34
                                                                                                                                      v35
                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError)))
                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                               else coe
                                                                      seq (coe v13)
                                                                      (coe
                                                                         MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40
                                                                         (coe
                                                                            MAlonzo.Code.VerifiedCompilation.Certificate.C_forceDelayT_8)
                                                                         v2 v3)
                                                        _ -> MAlonzo.RTE.mazUnreachableError))
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                _ -> MAlonzo.RTE.mazUnreachableError)
      C__'183'__92 v4 v5
        -> let v6
                 = coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__76
                     (coe
                        MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isLambda'63'_70
                        (\ v6 v7 ->
                           coe
                             MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)
                        (coe v2))
                     (coe
                        MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isLambda'63'_70
                        (\ v6 v7 ->
                           coe
                             MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)
                        (coe v3)) in
           coe
             (case coe v6 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                  -> if coe v7
                       then case coe v8 of
                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v9
                                -> case coe v9 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                       -> case coe v10 of
                                            MAlonzo.Code.VerifiedCompilation.UntypedViews.C_islambda_62 v13
                                              -> case coe v2 of
                                                   MAlonzo.Code.Untyped.C_ƛ_20 v14
                                                     -> coe
                                                          seq (coe v13)
                                                          (case coe v11 of
                                                             MAlonzo.Code.VerifiedCompilation.UntypedViews.C_islambda_62 v16
                                                               -> case coe v3 of
                                                                    MAlonzo.Code.Untyped.C_ƛ_20 v17
                                                                      -> coe
                                                                           seq (coe v16)
                                                                           (let v18
                                                                                  = coe
                                                                                      du_isFD'63'_186
                                                                                      (coe
                                                                                         MAlonzo.Code.VerifiedCompilation.Equality.du_DecEq'45'Maybe_122
                                                                                         (coe v0))
                                                                                      (coe
                                                                                         du_zipwk_94
                                                                                         (coe v4))
                                                                                      (coe v14)
                                                                                      (coe v17) in
                                                                            coe
                                                                              (case coe v18 of
                                                                                 MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32 v19
                                                                                   -> coe
                                                                                        MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32
                                                                                        (coe
                                                                                           C_abs_128
                                                                                           v19)
                                                                                 MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40 v22 v23 v24
                                                                                   -> case coe v4 of
                                                                                        C_'9633'_88
                                                                                          -> let v25
                                                                                                   = coe
                                                                                                       du_isForceDelay'63'_178
                                                                                                       (coe
                                                                                                          MAlonzo.Code.VerifiedCompilation.Equality.du_DecEq'45'Maybe_122
                                                                                                          (coe
                                                                                                             v0))
                                                                                                       v14
                                                                                                       v17 in
                                                                                             coe
                                                                                               (case coe
                                                                                                       v25 of
                                                                                                  MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32 v26
                                                                                                    -> coe
                                                                                                         MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32
                                                                                                         (coe
                                                                                                            C_last'45'abs_132
                                                                                                            v26)
                                                                                                  MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40 v29 v30 v31
                                                                                                    -> coe
                                                                                                         MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40
                                                                                                         v29
                                                                                                         v30
                                                                                                         v31
                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                        C_force_90 v25
                                                                                          -> coe
                                                                                               MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40
                                                                                               v22
                                                                                               v23
                                                                                               v24
                                                                                        C__'183'__92 v25 v26
                                                                                          -> coe
                                                                                               MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40
                                                                                               v22
                                                                                               v23
                                                                                               v24
                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError))
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       else coe
                              seq (coe v8)
                              (let v9
                                     = coe
                                         MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isForce'63'_284
                                         erased
                                         (\ v9 v10 ->
                                            coe
                                              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)
                                         (coe v2) in
                               coe
                                 (case coe v9 of
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                      -> if coe v10
                                           then case coe v11 of
                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v12
                                                    -> case coe v12 of
                                                         MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isforce_276 v14
                                                           -> case coe v2 of
                                                                MAlonzo.Code.Untyped.C_force_24 v15
                                                                  -> coe
                                                                       seq (coe v14)
                                                                       (let v16
                                                                              = coe
                                                                                  MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isDelay'63'_370
                                                                                  erased
                                                                                  (\ v16 v17 ->
                                                                                     coe
                                                                                       MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)
                                                                                  (coe v15) in
                                                                        coe
                                                                          (case coe v16 of
                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                               -> if coe v17
                                                                                    then case coe
                                                                                                v18 of
                                                                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v19
                                                                                             -> case coe
                                                                                                       v19 of
                                                                                                  MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isdelay_362 v21
                                                                                                    -> case coe
                                                                                                              v15 of
                                                                                                         MAlonzo.Code.Untyped.C_delay_26 v22
                                                                                                           -> let v23
                                                                                                                    = seq
                                                                                                                        (coe
                                                                                                                           v21)
                                                                                                                        (let v23
                                                                                                                               = coe
                                                                                                                                   du_isFD'63'_186
                                                                                                                                   (coe
                                                                                                                                      v0)
                                                                                                                                   (coe
                                                                                                                                      v1)
                                                                                                                                   (coe
                                                                                                                                      v22)
                                                                                                                                   (coe
                                                                                                                                      v3) in
                                                                                                                         coe
                                                                                                                           (case coe
                                                                                                                                   v23 of
                                                                                                                              MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32 v24
                                                                                                                                -> coe
                                                                                                                                     MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32
                                                                                                                                     (coe
                                                                                                                                        C_delay_124
                                                                                                                                        v24)
                                                                                                                              MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40 v27 v28 v29
                                                                                                                                -> coe
                                                                                                                                     MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40
                                                                                                                                     v27
                                                                                                                                     v28
                                                                                                                                     v29
                                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError)) in
                                                                                                              coe
                                                                                                                (case coe
                                                                                                                        v23 of
                                                                                                                   MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32 v24
                                                                                                                     -> coe
                                                                                                                          MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32
                                                                                                                          (coe
                                                                                                                             C_force_122
                                                                                                                             v24)
                                                                                                                   MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40 v27 v28 v29
                                                                                                                     -> coe
                                                                                                                          MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40
                                                                                                                          v27
                                                                                                                          v28
                                                                                                                          v29
                                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                                    else (let v19
                                                                                                = seq
                                                                                                    (coe
                                                                                                       v18)
                                                                                                    (let v19
                                                                                                           = coe
                                                                                                               MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isForce'63'_284
                                                                                                               erased
                                                                                                               (\ v19
                                                                                                                  v20 ->
                                                                                                                  coe
                                                                                                                    MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)
                                                                                                               (coe
                                                                                                                  v15) in
                                                                                                     coe
                                                                                                       (case coe
                                                                                                               v19 of
                                                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                                                                            -> if coe
                                                                                                                    v20
                                                                                                                 then case coe
                                                                                                                             v21 of
                                                                                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v22
                                                                                                                          -> case coe
                                                                                                                                    v22 of
                                                                                                                               MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isforce_276 v24
                                                                                                                                 -> case coe
                                                                                                                                           v15 of
                                                                                                                                      MAlonzo.Code.Untyped.C_force_24 v25
                                                                                                                                        -> coe
                                                                                                                                             seq
                                                                                                                                             (coe
                                                                                                                                                v24)
                                                                                                                                             (let v26
                                                                                                                                                    = coe
                                                                                                                                                        du_isFD'63'_186
                                                                                                                                                        (coe
                                                                                                                                                           v0)
                                                                                                                                                        (coe
                                                                                                                                                           C_force_90
                                                                                                                                                           (coe
                                                                                                                                                              C_force_90
                                                                                                                                                              (coe
                                                                                                                                                                 v1)))
                                                                                                                                                        (coe
                                                                                                                                                           v25)
                                                                                                                                                        (coe
                                                                                                                                                           v3) in
                                                                                                                                              coe
                                                                                                                                                (case coe
                                                                                                                                                        v26 of
                                                                                                                                                   MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32 v27
                                                                                                                                                     -> coe
                                                                                                                                                          MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32
                                                                                                                                                          (coe
                                                                                                                                                             C_force_122
                                                                                                                                                             v27)
                                                                                                                                                   MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40 v30 v31 v32
                                                                                                                                                     -> coe
                                                                                                                                                          MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40
                                                                                                                                                          v30
                                                                                                                                                          v31
                                                                                                                                                          v32
                                                                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                 else coe
                                                                                                                        seq
                                                                                                                        (coe
                                                                                                                           v21)
                                                                                                                        (let v22
                                                                                                                               = coe
                                                                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__76
                                                                                                                                   (coe
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
                                                                                                                                         v15))
                                                                                                                                   (coe
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
                                                                                                                                         v3)) in
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
                                                                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                                                                                                                     -> case coe
                                                                                                                                                               v26 of
                                                                                                                                                          MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isapp_154 v30 v31
                                                                                                                                                            -> case coe
                                                                                                                                                                      v15 of
                                                                                                                                                                 MAlonzo.Code.Untyped.C__'183'__22 v32 v33
                                                                                                                                                                   -> coe
                                                                                                                                                                        seq
                                                                                                                                                                        (coe
                                                                                                                                                                           v30)
                                                                                                                                                                        (coe
                                                                                                                                                                           seq
                                                                                                                                                                           (coe
                                                                                                                                                                              v31)
                                                                                                                                                                           (case coe
                                                                                                                                                                                   v27 of
                                                                                                                                                                              MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isapp_154 v36 v37
                                                                                                                                                                                -> case coe
                                                                                                                                                                                          v3 of
                                                                                                                                                                                     MAlonzo.Code.Untyped.C__'183'__22 v38 v39
                                                                                                                                                                                       -> coe
                                                                                                                                                                                            seq
                                                                                                                                                                                            (coe
                                                                                                                                                                                               v36)
                                                                                                                                                                                            (coe
                                                                                                                                                                                               seq
                                                                                                                                                                                               (coe
                                                                                                                                                                                                  v37)
                                                                                                                                                                                               (let v40
                                                                                                                                                                                                      = coe
                                                                                                                                                                                                          du_isForceDelay'63'_178
                                                                                                                                                                                                          v0
                                                                                                                                                                                                          v33
                                                                                                                                                                                                          v39 in
                                                                                                                                                                                                coe
                                                                                                                                                                                                  (case coe
                                                                                                                                                                                                          v40 of
                                                                                                                                                                                                     MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32 v41
                                                                                                                                                                                                       -> let v42
                                                                                                                                                                                                                = coe
                                                                                                                                                                                                                    du_isFD'63'_186
                                                                                                                                                                                                                    (coe
                                                                                                                                                                                                                       v0)
                                                                                                                                                                                                                    (coe
                                                                                                                                                                                                                       C__'183'__92
                                                                                                                                                                                                                       (coe
                                                                                                                                                                                                                          C_force_90
                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                             v1))
                                                                                                                                                                                                                       (coe
                                                                                                                                                                                                                          v39))
                                                                                                                                                                                                                    (coe
                                                                                                                                                                                                                       v32)
                                                                                                                                                                                                                    (coe
                                                                                                                                                                                                                       v38) in
                                                                                                                                                                                                          coe
                                                                                                                                                                                                            (case coe
                                                                                                                                                                                                                    v42 of
                                                                                                                                                                                                               MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32 v43
                                                                                                                                                                                                                 -> coe
                                                                                                                                                                                                                      MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32
                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                         C_app_126
                                                                                                                                                                                                                         v43
                                                                                                                                                                                                                         v41)
                                                                                                                                                                                                               MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40 v46 v47 v48
                                                                                                                                                                                                                 -> coe
                                                                                                                                                                                                                      MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40
                                                                                                                                                                                                                      v46
                                                                                                                                                                                                                      v47
                                                                                                                                                                                                                      v48
                                                                                                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                                                                                     MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40 v44 v45 v46
                                                                                                                                                                                                       -> coe
                                                                                                                                                                                                            MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40
                                                                                                                                                                                                            v44
                                                                                                                                                                                                            v45
                                                                                                                                                                                                            v46
                                                                                                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError)))
                                                                                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
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
                                                                                                                                               v15
                                                                                                                                               v3)
                                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError)) in
                                                                                          coe
                                                                                            (case coe
                                                                                                    v19 of
                                                                                               MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32 v20
                                                                                                 -> coe
                                                                                                      MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32
                                                                                                      (coe
                                                                                                         C_force_122
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
                                                  (let v12
                                                         = coe
                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__76
                                                             (coe
                                                                MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isApp'63'_166
                                                                erased
                                                                (\ v12 v13 ->
                                                                   coe
                                                                     MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)
                                                                (\ v12 v13 ->
                                                                   coe
                                                                     MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)
                                                                (coe v2))
                                                             (coe
                                                                MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isApp'63'_166
                                                                erased
                                                                (\ v12 v13 ->
                                                                   coe
                                                                     MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)
                                                                (\ v12 v13 ->
                                                                   coe
                                                                     MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)
                                                                (coe v3)) in
                                                   coe
                                                     (case coe v12 of
                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                                          -> if coe v13
                                                               then case coe v14 of
                                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v15
                                                                        -> case coe v15 of
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                               -> case coe v16 of
                                                                                    MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isapp_154 v20 v21
                                                                                      -> case coe
                                                                                                v2 of
                                                                                           MAlonzo.Code.Untyped.C__'183'__22 v22 v23
                                                                                             -> coe
                                                                                                  seq
                                                                                                  (coe
                                                                                                     v20)
                                                                                                  (coe
                                                                                                     seq
                                                                                                     (coe
                                                                                                        v21)
                                                                                                     (case coe
                                                                                                             v17 of
                                                                                                        MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isapp_154 v26 v27
                                                                                                          -> case coe
                                                                                                                    v3 of
                                                                                                               MAlonzo.Code.Untyped.C__'183'__22 v28 v29
                                                                                                                 -> coe
                                                                                                                      seq
                                                                                                                      (coe
                                                                                                                         v26)
                                                                                                                      (coe
                                                                                                                         seq
                                                                                                                         (coe
                                                                                                                            v27)
                                                                                                                         (let v30
                                                                                                                                = coe
                                                                                                                                    du_isForceDelay'63'_178
                                                                                                                                    v0
                                                                                                                                    v23
                                                                                                                                    v29 in
                                                                                                                          coe
                                                                                                                            (case coe
                                                                                                                                    v30 of
                                                                                                                               MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32 v31
                                                                                                                                 -> let v32
                                                                                                                                          = coe
                                                                                                                                              du_isFD'63'_186
                                                                                                                                              (coe
                                                                                                                                                 v0)
                                                                                                                                              (coe
                                                                                                                                                 C__'183'__92
                                                                                                                                                 (coe
                                                                                                                                                    v1)
                                                                                                                                                 (coe
                                                                                                                                                    v29))
                                                                                                                                              (coe
                                                                                                                                                 v22)
                                                                                                                                              (coe
                                                                                                                                                 v28) in
                                                                                                                                    coe
                                                                                                                                      (case coe
                                                                                                                                              v32 of
                                                                                                                                         MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32 v33
                                                                                                                                           -> coe
                                                                                                                                                MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_32
                                                                                                                                                (coe
                                                                                                                                                   C_app_126
                                                                                                                                                   v33
                                                                                                                                                   v31)
                                                                                                                                         MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40 v36 v37 v38
                                                                                                                                           -> coe
                                                                                                                                                MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40
                                                                                                                                                v36
                                                                                                                                                v37
                                                                                                                                                v38
                                                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                               MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40 v34 v35 v36
                                                                                                                                 -> coe
                                                                                                                                      MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40
                                                                                                                                      v34
                                                                                                                                      v35
                                                                                                                                      v36
                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError)))
                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                               else coe
                                                                      seq (coe v14)
                                                                      (coe
                                                                         MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_40
                                                                         (coe
                                                                            MAlonzo.Code.VerifiedCompilation.Certificate.C_forceDelayT_8)
                                                                         v2 v3)
                                                        _ -> MAlonzo.RTE.mazUnreachableError))
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.UForceDelay..extendedlambda0
d_'46'extendedlambda0_228 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (T_FD_116 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4 ->
  AgdaAny ->
  AgdaAny -> T_FD_116 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda0_228 = erased
-- VerifiedCompilation.UForceDelay..extendedlambda1
d_'46'extendedlambda1_250 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isForce_268 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  T_FD_116 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda1_250 = erased
-- VerifiedCompilation.UForceDelay..extendedlambda2
d_'46'extendedlambda2_298 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isForce_268 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_FD_116 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda2_298 = erased
-- VerifiedCompilation.UForceDelay..extendedlambda3
d_'46'extendedlambda3_366 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (T_FD_116 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_16 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isForce_268 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_FD_116 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda3_366 = erased
-- VerifiedCompilation.UForceDelay..extendedlambda4
d_'46'extendedlambda4_440 ::
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
  (T_FD_116 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4 ->
  AgdaAny ->
  AgdaAny -> T_FD_116 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda4_440 = erased
-- VerifiedCompilation.UForceDelay..extendedlambda5
d_'46'extendedlambda5_472 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  T_Zipper_84 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (T_FD_116 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4 ->
  AgdaAny ->
  AgdaAny -> T_FD_116 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda5_472 = erased
-- VerifiedCompilation.UForceDelay..extendedlambda6
d_'46'extendedlambda6_490 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  T_Zipper_84 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (T_FD_116 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4 ->
  AgdaAny ->
  AgdaAny -> T_FD_116 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda6_490 = erased
-- VerifiedCompilation.UForceDelay..extendedlambda7
d_'46'extendedlambda7_550 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  T_Zipper_84 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (T_FD_116 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isDelay_354 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_FD_116 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda7_550 = erased
-- VerifiedCompilation.UForceDelay..extendedlambda8
d_'46'extendedlambda8_580 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isForce_268 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isDelay_354 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  T_Zipper_84 ->
  T_FD_116 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda8_580 = erased
-- VerifiedCompilation.UForceDelay..extendedlambda9
d_'46'extendedlambda9_640 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isForce_268 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isDelay_354 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_Zipper_84 ->
  T_FD_116 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda9_640 = erased
-- VerifiedCompilation.UForceDelay..extendedlambda10
d_'46'extendedlambda10_720 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  T_Zipper_84 ->
  (T_FD_116 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_16 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isForce_268 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isDelay_354 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_FD_116 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda10_720 = erased
-- VerifiedCompilation.UForceDelay..extendedlambda11
d_'46'extendedlambda11_812 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4 ->
  AgdaAny ->
  AgdaAny ->
  (T_FD_116 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  T_FD_116 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda11_812 = erased
-- VerifiedCompilation.UForceDelay..extendedlambda12
d_'46'extendedlambda12_828 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  T_Zipper_84 ->
  (T_FD_116 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  T_FD_116 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda12_828 = erased
-- VerifiedCompilation.UForceDelay..extendedlambda13
d_'46'extendedlambda13_844 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  T_Zipper_84 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (T_FD_116 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  T_FD_116 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda13_844 = erased
-- VerifiedCompilation.UForceDelay..extendedlambda14
d_'46'extendedlambda14_912 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  T_Zipper_84 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (T_FD_116 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_FD_116 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda14_912 = erased
-- VerifiedCompilation.UForceDelay..extendedlambda15
d_'46'extendedlambda15_946 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isForce_268 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  T_Zipper_84 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  T_FD_116 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda15_946 = erased
-- VerifiedCompilation.UForceDelay..extendedlambda16
d_'46'extendedlambda16_1008 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isForce_268 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_Zipper_84 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  T_FD_116 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda16_1008 = erased
-- VerifiedCompilation.UForceDelay..extendedlambda17
d_'46'extendedlambda17_1094 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Equality.T_DecEq_6 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  T_Zipper_84 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (T_FD_116 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_16 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isForce_268 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_FD_116 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda17_1094 = erased
