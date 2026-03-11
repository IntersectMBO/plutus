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

module MAlonzo.Code.CertifierReport where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Untyped
import qualified MAlonzo.Code.Untyped.RenamingSubstitution
import qualified MAlonzo.Code.Utils
import qualified MAlonzo.Code.VerifiedCompilation
import qualified MAlonzo.Code.VerifiedCompilation.Certificate
import qualified MAlonzo.Code.VerifiedCompilation.UInline
import qualified MAlonzo.Code.VerifiedCompilation.UntypedTranslation

-- CertifierReport.⇉_
d_'8649'__2 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_'8649'__2 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("  " :: Data.Text.Text) v0
-- CertifierReport.nl
d_nl_6 :: MAlonzo.Code.Agda.Builtin.String.T_String_6
d_nl_6 = coe ("\n" :: Data.Text.Text)
-- CertifierReport.hl
d_hl_8 :: MAlonzo.Code.Agda.Builtin.String.T_String_6
d_hl_8
  = coe
      ("\n\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\n"
       ::
       Data.Text.Text)
-- CertifierReport.showTag
d_showTag_10 ::
  MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showTag_10 v0
  = case coe v0 of
      MAlonzo.Code.VerifiedCompilation.Certificate.C_floatDelayT_6
        -> coe ("Float Delay" :: Data.Text.Text)
      MAlonzo.Code.VerifiedCompilation.Certificate.C_forceDelayT_8
        -> coe ("Force-Delay Cancellation" :: Data.Text.Text)
      MAlonzo.Code.VerifiedCompilation.Certificate.C_forceCaseDelayT_10
        -> coe ("Float Force into Case Branches" :: Data.Text.Text)
      MAlonzo.Code.VerifiedCompilation.Certificate.C_caseOfCaseT_12
        -> coe ("Case-of-Case" :: Data.Text.Text)
      MAlonzo.Code.VerifiedCompilation.Certificate.C_caseReduceT_14
        -> coe
             ("Case-Constr and Case-Constant Cancellation" :: Data.Text.Text)
      MAlonzo.Code.VerifiedCompilation.Certificate.C_inlineT_16
        -> coe ("Inlining" :: Data.Text.Text)
      MAlonzo.Code.VerifiedCompilation.Certificate.C_cseT_18
        -> coe ("Common Subexpression Elimination" :: Data.Text.Text)
      MAlonzo.Code.VerifiedCompilation.Certificate.C_applyToCaseT_20
        -> coe
             ("Transform multi-argument applications into case-constr form"
              ::
              Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- CertifierReport.numSites′
d_numSites'8242'_20 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_12 ->
  Integer
d_numSites'8242'_20 ~v0 v1 v2 v3 = du_numSites'8242'_20 v1 v2 v3
du_numSites'8242'_20 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_12 ->
  Integer
du_numSites'8242'_20 v0 v1 v2
  = coe
      du_go_34 (coe v0) (coe v1) (coe v2) (coe v0) (coe v1) (coe v2)
      (coe (0 :: Integer))
-- CertifierReport._.go
d_go_34 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Integer ->
  MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_12 ->
  Integer
d_go_34 ~v0 v1 v2 v3 ~v4 v5 v6 v7 v8 v9
  = du_go_34 v1 v2 v3 v5 v6 v7 v8 v9
du_go_34 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Integer ->
  MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_12 ->
  Integer
du_go_34 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_istranslation_92 v10
        -> coe addInt (coe (1 :: Integer)) (coe v6)
      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_match_98 v10
        -> coe
             du_go'7504'_44 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v10)
      _ -> MAlonzo.RTE.mazUnreachableError
-- CertifierReport._.goᵐ
d_go'7504'_44 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Integer ->
  MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_TransMatch_18 ->
  Integer
d_go'7504'_44 ~v0 v1 v2 v3 ~v4 v5 v6 v7 v8 v9
  = du_go'7504'_44 v1 v2 v3 v5 v6 v7 v8 v9
du_go'7504'_44 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Integer ->
  MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_TransMatch_18 ->
  Integer
du_go'7504'_44 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_var_26
        -> coe v6
      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_ƛ_32 v10
        -> case coe v4 of
             MAlonzo.Code.Untyped.C_ƛ_20 v11
               -> case coe v5 of
                    MAlonzo.Code.Untyped.C_ƛ_20 v12
                      -> coe
                           du_go_34 (coe v0) (coe v1) (coe v2)
                           (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v11) (coe v12)
                           (coe v6) (coe v10)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_app_42 v12 v13
        -> case coe v4 of
             MAlonzo.Code.Untyped.C__'183'__22 v14 v15
               -> case coe v5 of
                    MAlonzo.Code.Untyped.C__'183'__22 v16 v17
                      -> coe
                           du_go_34 (coe v0) (coe v1) (coe v2) (coe v3) (coe v15) (coe v17)
                           (coe
                              du_go_34 (coe v0) (coe v1) (coe v2) (coe v3) (coe v14) (coe v16)
                              (coe v6) (coe v12))
                           (coe v13)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_force_48 v10
        -> case coe v4 of
             MAlonzo.Code.Untyped.C_force_24 v11
               -> case coe v5 of
                    MAlonzo.Code.Untyped.C_force_24 v12
                      -> coe
                           du_go_34 (coe v0) (coe v1) (coe v2) (coe v3) (coe v11) (coe v12)
                           (coe v6) (coe v10)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_delay_54 v10
        -> case coe v4 of
             MAlonzo.Code.Untyped.C_delay_26 v11
               -> case coe v5 of
                    MAlonzo.Code.Untyped.C_delay_26 v12
                      -> coe
                           du_go_34 (coe v0) (coe v1) (coe v2) (coe v3) (coe v11) (coe v12)
                           (coe v6) (coe v10)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_con_58
        -> coe v6
      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_constr_66 v11
        -> case coe v4 of
             MAlonzo.Code.Untyped.C_constr_34 v12 v13
               -> case coe v5 of
                    MAlonzo.Code.Untyped.C_constr_34 v14 v15
                      -> coe
                           du_go'7510''695'_54 (coe v0) (coe v1) (coe v2) (coe v3) (coe v13)
                           (coe v15) (coe v6) (coe v11)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_case_76 v12 v13
        -> case coe v4 of
             MAlonzo.Code.Untyped.C_case_40 v14 v15
               -> case coe v5 of
                    MAlonzo.Code.Untyped.C_case_40 v16 v17
                      -> coe
                           du_go_34 (coe v0) (coe v1) (coe v2) (coe v3) (coe v14) (coe v16)
                           (coe
                              du_go'7510''695'_54 (coe v0) (coe v1) (coe v2) (coe v3) (coe v15)
                              (coe v17) (coe v6) (coe v12))
                           (coe v13)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_builtin_80
        -> coe v6
      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_error_82
        -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- CertifierReport._.goᵖʷ
d_go'7510''695'_54 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  Integer
d_go'7510''695'_54 ~v0 v1 v2 v3 ~v4 v5 v6 v7 v8 v9
  = du_go'7510''695'_54 v1 v2 v3 v5 v6 v7 v8 v9
du_go'7510''695'_54 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  Integer
du_go'7510''695'_54 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C_'91''93'_56
        -> coe v6
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v12 v13
        -> case coe v4 of
             (:) v14 v15
               -> case coe v5 of
                    (:) v16 v17
                      -> coe
                           du_go'7510''695'_54 (coe v0) (coe v1) (coe v2) (coe v3) (coe v15)
                           (coe v17)
                           (coe
                              du_go_34 (coe v0) (coe v1) (coe v2) (coe v3) (coe v14) (coe v16)
                              (coe v6) (coe v12))
                           (coe v13)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- CertifierReport.numSitesInlineᵖʷ
d_numSitesInline'7510''695'_116 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  Integer
d_numSitesInline'7510''695'_116 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C_'91''93'_56
        -> coe (0 :: Integer)
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v9 v10
        -> case coe v2 of
             (:) v11 v12
               -> case coe v3 of
                    (:) v13 v14
                      -> coe
                           addInt
                           (coe
                              d_numSitesInline_134 (coe v0) (coe v1)
                              (coe MAlonzo.Code.VerifiedCompilation.UInline.C_'9633'_32)
                              (coe MAlonzo.Code.VerifiedCompilation.UInline.C_'9633'_32)
                              (coe MAlonzo.Code.VerifiedCompilation.UInline.C_'9633'_106)
                              (coe v11) (coe v13) (coe v9))
                           (coe
                              d_numSitesInline'7510''695'_116 (coe v0) (coe v1) (coe v12)
                              (coe v14) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- CertifierReport.numSitesInline
d_numSitesInline_134 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  MAlonzo.Code.VerifiedCompilation.UInline.T__'8605'_28 ->
  MAlonzo.Code.VerifiedCompilation.UInline.T__'8605'_28 ->
  MAlonzo.Code.VerifiedCompilation.UInline.T__'8829'__102 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.UInline.T_Inline_224 -> Integer
d_numSitesInline_134 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.VerifiedCompilation.UInline.C_'96'_230
        -> coe (0 :: Integer)
      MAlonzo.Code.VerifiedCompilation.UInline.C_'96''8595'_234 v14
        -> case coe v5 of
             MAlonzo.Code.Untyped.C_'96'_18 v15
               -> coe
                    addInt (coe (1 :: Integer))
                    (coe
                       d_numSitesInline_134 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v1 v15) (coe v6) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.VerifiedCompilation.UInline.C_ƛ'9633'_236 v11
        -> case coe v5 of
             MAlonzo.Code.Untyped.C_ƛ_20 v12
               -> case coe v6 of
                    MAlonzo.Code.Untyped.C_ƛ_20 v13
                      -> coe
                           d_numSitesInline_134 (coe addInt (coe (1 :: Integer)) (coe v0))
                           (coe
                              MAlonzo.Code.Untyped.RenamingSubstitution.du_lifts_378 (coe v0)
                              (coe v1))
                           (coe MAlonzo.Code.VerifiedCompilation.UInline.C_'9633'_32)
                           (coe MAlonzo.Code.VerifiedCompilation.UInline.C_'9633'_32)
                           (coe MAlonzo.Code.VerifiedCompilation.UInline.C_'9633'_106)
                           (coe v12) (coe v13) (coe v11)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.VerifiedCompilation.UInline.C_ƛ_240 v15
        -> case coe v2 of
             MAlonzo.Code.VerifiedCompilation.UInline.C__'183'__34 v16 v17
               -> case coe v3 of
                    MAlonzo.Code.VerifiedCompilation.UInline.C__'183'__34 v18 v19
                      -> case coe v4 of
                           MAlonzo.Code.VerifiedCompilation.UInline.C_keep_114 v23
                             -> case coe v5 of
                                  MAlonzo.Code.Untyped.C_ƛ_20 v24
                                    -> case coe v6 of
                                         MAlonzo.Code.Untyped.C_ƛ_20 v25
                                           -> coe
                                                d_numSitesInline_134
                                                (coe addInt (coe (1 :: Integer)) (coe v0))
                                                (coe
                                                   MAlonzo.Code.Untyped.RenamingSubstitution.du_extend_454
                                                   (coe
                                                      MAlonzo.Code.Untyped.RenamingSubstitution.du__'8593''738'_470
                                                      (coe v0) (coe v1))
                                                   (coe
                                                      MAlonzo.Code.Untyped.RenamingSubstitution.d_weaken_88
                                                      (coe v0) (coe v17)))
                                                (coe
                                                   MAlonzo.Code.VerifiedCompilation.UInline.d__'8593''7611'_40
                                                   (coe v0) (coe v16))
                                                (coe
                                                   MAlonzo.Code.VerifiedCompilation.UInline.d__'8593''7611'_40
                                                   (coe v0) (coe v18))
                                                (coe
                                                   MAlonzo.Code.VerifiedCompilation.UInline.du__'8593''7611''7611'_126
                                                   (coe v16) (coe v18) (coe v23))
                                                (coe v24) (coe v25) (coe v15)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.VerifiedCompilation.UInline.C_ƛ'8595'_244 v15
        -> case coe v2 of
             MAlonzo.Code.VerifiedCompilation.UInline.C__'183'__34 v16 v17
               -> case coe v3 of
                    MAlonzo.Code.VerifiedCompilation.UInline.C__'183'__34 v18 v19
                      -> case coe v4 of
                           MAlonzo.Code.VerifiedCompilation.UInline.C_drop_122 v23
                             -> case coe v5 of
                                  MAlonzo.Code.Untyped.C_ƛ_20 v24
                                    -> coe
                                         d_numSitesInline_134
                                         (coe addInt (coe (1 :: Integer)) (coe v0))
                                         (coe
                                            MAlonzo.Code.Untyped.RenamingSubstitution.du_extend_454
                                            (coe
                                               MAlonzo.Code.Untyped.RenamingSubstitution.du__'8593''738'_470
                                               (coe v0) (coe v1))
                                            (coe
                                               MAlonzo.Code.Untyped.RenamingSubstitution.d_weaken_88
                                               (coe v0) (coe v17)))
                                         (coe
                                            MAlonzo.Code.VerifiedCompilation.UInline.d__'8593''7611'_40
                                            (coe v0) (coe v16))
                                         (coe
                                            MAlonzo.Code.VerifiedCompilation.UInline.d__'8593''7611'_40
                                            (coe v0) (coe v18))
                                         (coe
                                            MAlonzo.Code.VerifiedCompilation.UInline.du__'8593''7611''7611'_126
                                            (coe v16) (coe v18) (coe v23))
                                         (coe v24)
                                         (coe
                                            MAlonzo.Code.Untyped.RenamingSubstitution.d_weaken_88
                                            (coe v0) (coe v6))
                                         (coe v15)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.VerifiedCompilation.UInline.C__'183'__250 v16 v17
        -> case coe v5 of
             MAlonzo.Code.Untyped.C__'183'__22 v18 v19
               -> case coe v6 of
                    MAlonzo.Code.Untyped.C__'183'__22 v20 v21
                      -> coe
                           addInt
                           (coe
                              d_numSitesInline_134 (coe v0) (coe v1)
                              (coe MAlonzo.Code.VerifiedCompilation.UInline.C_'9633'_32)
                              (coe MAlonzo.Code.VerifiedCompilation.UInline.C_'9633'_32)
                              (coe MAlonzo.Code.VerifiedCompilation.UInline.C_'9633'_106)
                              (coe v19) (coe v21) (coe v17))
                           (coe
                              d_numSitesInline_134 (coe v0) (coe v1)
                              (coe
                                 MAlonzo.Code.VerifiedCompilation.UInline.C__'183'__34 (coe v2)
                                 (coe v19))
                              (coe
                                 MAlonzo.Code.VerifiedCompilation.UInline.C__'183'__34 (coe v3)
                                 (coe v19))
                              (coe MAlonzo.Code.VerifiedCompilation.UInline.C_keep_114 v4)
                              (coe v18) (coe v20) (coe v16))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.VerifiedCompilation.UInline.C__'183''8595'_254 v15
        -> case coe v5 of
             MAlonzo.Code.Untyped.C__'183'__22 v16 v17
               -> coe
                    d_numSitesInline_134 (coe v0) (coe v1)
                    (coe
                       MAlonzo.Code.VerifiedCompilation.UInline.C__'183'__34 (coe v2)
                       (coe v17))
                    (coe
                       MAlonzo.Code.VerifiedCompilation.UInline.C__'183'__34 (coe v3)
                       (coe v17))
                    (coe MAlonzo.Code.VerifiedCompilation.UInline.C_drop_122 v4)
                    (coe v16) (coe v6) (coe v15)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.VerifiedCompilation.UInline.C_force_258 v14
        -> case coe v5 of
             MAlonzo.Code.Untyped.C_force_24 v15
               -> case coe v6 of
                    MAlonzo.Code.Untyped.C_force_24 v16
                      -> coe
                           d_numSitesInline_134 (coe v0) (coe v1)
                           (coe MAlonzo.Code.VerifiedCompilation.UInline.C_'9633'_32)
                           (coe MAlonzo.Code.VerifiedCompilation.UInline.C_'9633'_32)
                           (coe MAlonzo.Code.VerifiedCompilation.UInline.C_'9633'_106)
                           (coe v15) (coe v16) (coe v14)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.VerifiedCompilation.UInline.C_delay_262 v14
        -> case coe v5 of
             MAlonzo.Code.Untyped.C_delay_26 v15
               -> case coe v6 of
                    MAlonzo.Code.Untyped.C_delay_26 v16
                      -> coe
                           d_numSitesInline_134 (coe v0) (coe v1)
                           (coe MAlonzo.Code.VerifiedCompilation.UInline.C_'9633'_32)
                           (coe MAlonzo.Code.VerifiedCompilation.UInline.C_'9633'_32)
                           (coe MAlonzo.Code.VerifiedCompilation.UInline.C_'9633'_106)
                           (coe v15) (coe v16) (coe v14)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.VerifiedCompilation.UInline.C_con_266
        -> coe (0 :: Integer)
      MAlonzo.Code.VerifiedCompilation.UInline.C_builtin_270
        -> coe (0 :: Integer)
      MAlonzo.Code.VerifiedCompilation.UInline.C_constr_280 v15
        -> case coe v5 of
             MAlonzo.Code.Untyped.C_constr_34 v16 v17
               -> case coe v6 of
                    MAlonzo.Code.Untyped.C_constr_34 v18 v19
                      -> coe
                           d_numSitesInline'7510''695'_116 (coe v0) (coe v1) (coe v17)
                           (coe v19) (coe v15)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.VerifiedCompilation.UInline.C_case_290 v16 v17
        -> case coe v5 of
             MAlonzo.Code.Untyped.C_case_40 v18 v19
               -> case coe v6 of
                    MAlonzo.Code.Untyped.C_case_40 v20 v21
                      -> coe
                           addInt
                           (coe
                              d_numSitesInline_134 (coe v0) (coe v1)
                              (coe MAlonzo.Code.VerifiedCompilation.UInline.C_'9633'_32)
                              (coe MAlonzo.Code.VerifiedCompilation.UInline.C_'9633'_32)
                              (coe MAlonzo.Code.VerifiedCompilation.UInline.C_'9633'_106)
                              (coe v18) (coe v20) (coe v16))
                           (coe
                              d_numSitesInline'7510''695'_116 (coe v0) (coe v1) (coe v19)
                              (coe v21) (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.VerifiedCompilation.UInline.C_error_292
        -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- CertifierReport.numSites
d_numSites_174 ::
  Integer ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.T_Transformation_2 ->
  Maybe Integer
d_numSites_174 v0 ~v1 v2 v3 v4 = du_numSites_174 v0 v2 v3 v4
du_numSites_174 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.T_Transformation_2 ->
  Maybe Integer
du_numSites_174 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.VerifiedCompilation.C_isFD_10 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe du_numSites'8242'_20 v0 v1 v2 v7)
      MAlonzo.Code.VerifiedCompilation.C_isFlD_18 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe du_numSites'8242'_20 v0 v1 v2 v7)
      MAlonzo.Code.VerifiedCompilation.C_isCSE_26 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe du_numSites'8242'_20 v0 v1 v2 v7)
      MAlonzo.Code.VerifiedCompilation.C_isInline_32 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                d_numSitesInline_134 (coe (0 :: Integer)) erased
                (coe MAlonzo.Code.VerifiedCompilation.UInline.C_'9633'_32)
                (coe MAlonzo.Code.VerifiedCompilation.UInline.C_'9633'_32)
                (coe MAlonzo.Code.VerifiedCompilation.UInline.C_'9633'_106)
                (coe v1) (coe v2) (coe v6))
      MAlonzo.Code.VerifiedCompilation.C_isCaseReduce_40 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe du_numSites'8242'_20 v0 v1 v2 v7)
      MAlonzo.Code.VerifiedCompilation.C_forceCaseDelayNotImplemented_48
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.VerifiedCompilation.C_cocNotImplemented_56
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.VerifiedCompilation.C_applyToCaseNotImplemented_64
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- CertifierReport.showSites
d_showSites_194 ::
  Integer ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.T_Transformation_2 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showSites_194 v0 ~v1 v2 v3 v4 = du_showSites_194 v0 v2 v3 v4
du_showSites_194 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.T_Transformation_2 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_showSites_194 v0 v1 v2 v3
  = let v4
          = coe du_numSites_174 (coe v0) (coe v1) (coe v2) (coe v3) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
           -> coe
                d_'8649'__2
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("Optimization sites: " :: Data.Text.Text)
                   (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v5))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe ("" :: Data.Text.Text)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- CertifierReport.termSize
d_termSize_210 ::
  Integer -> MAlonzo.Code.Untyped.T__'8866'_14 -> Integer
d_termSize_210 v0 v1
  = case coe v1 of
      MAlonzo.Code.Untyped.C_'96'_18 v2 -> coe (1 :: Integer)
      MAlonzo.Code.Untyped.C_ƛ_20 v2
        -> coe
             addInt (coe (1 :: Integer))
             (coe
                d_termSize_210 (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v2))
      MAlonzo.Code.Untyped.C__'183'__22 v2 v3
        -> coe
             addInt
             (coe
                addInt (coe (1 :: Integer)) (coe d_termSize_210 (coe v0) (coe v2)))
             (coe d_termSize_210 (coe v0) (coe v3))
      MAlonzo.Code.Untyped.C_force_24 v2
        -> coe
             addInt (coe (1 :: Integer)) (coe d_termSize_210 (coe v0) (coe v2))
      MAlonzo.Code.Untyped.C_delay_26 v2
        -> coe
             addInt (coe (1 :: Integer)) (coe d_termSize_210 (coe v0) (coe v2))
      MAlonzo.Code.Untyped.C_con_28 v2 -> coe (1 :: Integer)
      MAlonzo.Code.Untyped.C_constr_34 v2 v3
        -> coe
             addInt (coe (1 :: Integer))
             (coe d_termSize'7510''695'_214 (coe v0) (coe v3))
      MAlonzo.Code.Untyped.C_case_40 v2 v3
        -> coe
             addInt
             (coe
                addInt (coe (1 :: Integer))
                (coe d_termSize'7510''695'_214 (coe v0) (coe v3)))
             (coe d_termSize_210 (coe v0) (coe v2))
      MAlonzo.Code.Untyped.C_builtin_44 v2 -> coe (1 :: Integer)
      MAlonzo.Code.Untyped.C_error_46 -> coe (1 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- CertifierReport.termSizeᵖʷ
d_termSize'7510''695'_214 ::
  Integer -> [MAlonzo.Code.Untyped.T__'8866'_14] -> Integer
d_termSize'7510''695'_214 v0 v1
  = case coe v1 of
      [] -> coe (0 :: Integer)
      (:) v2 v3
        -> coe
             addInt (coe d_termSize'7510''695'_214 (coe v0) (coe v3))
             (coe d_termSize_210 (coe v0) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- CertifierReport.reportPasses
d_reportPasses_244 ::
  Integer ->
  MAlonzo.Code.Utils.T_List_414
    (MAlonzo.Code.Utils.T__'215'__396
       MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4
       (MAlonzo.Code.Utils.T__'215'__396
          MAlonzo.Code.VerifiedCompilation.Certificate.T_Hints_50
          (MAlonzo.Code.Utils.T__'215'__396
             MAlonzo.Code.Untyped.T__'8866'_14
             MAlonzo.Code.Untyped.T__'8866'_14))) ->
  Integer ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_CertResult_64 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_reportPasses_244 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_70 v4
        -> case coe v4 of
             MAlonzo.Code.VerifiedCompilation.C_empty_72
               -> coe ("" :: Data.Text.Text)
             MAlonzo.Code.VerifiedCompilation.C_cons_86 v11 v12
               -> case coe v1 of
                    MAlonzo.Code.Utils.C__'8759'__420 v13 v14
                      -> case coe v13 of
                           MAlonzo.Code.Utils.C__'44'__410 v15 v16
                             -> case coe v16 of
                                  MAlonzo.Code.Utils.C__'44'__410 v17 v18
                                    -> case coe v18 of
                                         MAlonzo.Code.Utils.C__'44'__410 v19 v20
                                           -> coe
                                                MAlonzo.Code.Data.String.Base.d__'43''43'__20 d_hl_8
                                                (coe
                                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                   ("Pass " :: Data.Text.Text)
                                                   (coe
                                                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                      (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
                                                      (coe
                                                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                         (": " :: Data.Text.Text)
                                                         (coe
                                                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                            (d_showTag_10 (coe v15))
                                                            (coe
                                                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                               ("  \9989" :: Data.Text.Text)
                                                               (coe
                                                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                  d_hl_8
                                                                  (coe
                                                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                     (d_'8649'__2
                                                                        (coe
                                                                           ("Program Size Before: "
                                                                            ::
                                                                            Data.Text.Text)))
                                                                     (coe
                                                                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                        (coe
                                                                           MAlonzo.Code.Data.Nat.Show.d_show_56
                                                                           (d_termSize_210
                                                                              (coe v0) (coe v19)))
                                                                        (coe
                                                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                           d_nl_6
                                                                           (coe
                                                                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                              (d_'8649'__2
                                                                                 (coe
                                                                                    ("Program Size After: "
                                                                                     ::
                                                                                     Data.Text.Text)))
                                                                              (coe
                                                                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.Nat.Show.d_show_56
                                                                                    (d_termSize_210
                                                                                       (coe v0)
                                                                                       (coe v20)))
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                                    d_nl_6
                                                                                    (coe
                                                                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                                       (coe
                                                                                          du_showSites_194
                                                                                          (coe v0)
                                                                                          (coe v19)
                                                                                          (coe v20)
                                                                                          (coe v11))
                                                                                       (coe
                                                                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                                          d_nl_6
                                                                                          (d_reportPasses_244
                                                                                             (coe
                                                                                                v0)
                                                                                             (coe
                                                                                                v14)
                                                                                             (coe
                                                                                                addInt
                                                                                                (coe
                                                                                                   (1 ::
                                                                                                      Integer))
                                                                                                (coe
                                                                                                   v2))
                                                                                             (coe
                                                                                                MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_70
                                                                                                (coe
                                                                                                   v12)))))))))))))))))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_78 v7 v8 v9
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20 d_hl_8
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("Pass " :: Data.Text.Text)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (": " :: Data.Text.Text)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (d_showTag_10 (coe v7))
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            ("  \10060 FAILED" :: Data.Text.Text) d_hl_8)))))
      MAlonzo.Code.VerifiedCompilation.Certificate.C_abort_84 v6 v7 v8
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20 d_hl_8
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("Pass " :: Data.Text.Text)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (": " :: Data.Text.Text)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (d_showTag_10 (coe v6))
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            ("  \10060 FAILED" :: Data.Text.Text) d_hl_8)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- CertifierReport.makeReport
d_makeReport_272 ::
  Integer ->
  MAlonzo.Code.Utils.T_List_414
    (MAlonzo.Code.Utils.T__'215'__396
       MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4
       (MAlonzo.Code.Utils.T__'215'__396
          MAlonzo.Code.VerifiedCompilation.Certificate.T_Hints_50
          (MAlonzo.Code.Utils.T__'215'__396
             MAlonzo.Code.Untyped.T__'8866'_14
             MAlonzo.Code.Untyped.T__'8866'_14))) ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_CertResult_64 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_makeReport_272 v0 v1 v2
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("UPLC OPTIMIZATION: CERTIFIER REPORT" :: Data.Text.Text)
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20 d_nl_6
         (d_reportPasses_244
            (coe v0) (coe v1) (coe (1 :: Integer)) (coe v2)))
