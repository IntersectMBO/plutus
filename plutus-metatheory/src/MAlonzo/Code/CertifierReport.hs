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
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Untyped
import qualified MAlonzo.Code.Untyped.Relation.Binary.Core
import qualified MAlonzo.Code.Untyped.Relation.Binary.Modular
import qualified MAlonzo.Code.Untyped.RenamingSubstitution
import qualified MAlonzo.Code.Utils
import qualified MAlonzo.Code.VerifiedCompilation
import qualified MAlonzo.Code.VerifiedCompilation.Trace
import qualified MAlonzo.Code.VerifiedCompilation.UCaseReduce
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
-- CertifierReport.showCertifiedOptTag
d_showCertifiedOptTag_10 ::
  MAlonzo.Code.VerifiedCompilation.Trace.T_CertifiedOptTag_12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showCertifiedOptTag_10 v0
  = case coe v0 of
      MAlonzo.Code.VerifiedCompilation.Trace.C_floatDelayT_14
        -> coe ("Float Delay" :: Data.Text.Text)
      MAlonzo.Code.VerifiedCompilation.Trace.C_forceDelayT_16
        -> coe ("Force-Delay Cancellation" :: Data.Text.Text)
      MAlonzo.Code.VerifiedCompilation.Trace.C_forceCaseDelayT_18
        -> coe ("Float Force into Case Branches" :: Data.Text.Text)
      MAlonzo.Code.VerifiedCompilation.Trace.C_inlineT_20
        -> coe ("Inlining" :: Data.Text.Text)
      MAlonzo.Code.VerifiedCompilation.Trace.C_cseT_22
        -> coe ("Common Subexpression Elimination" :: Data.Text.Text)
      MAlonzo.Code.VerifiedCompilation.Trace.C_applyToCaseT_24
        -> coe
             ("Transform multi-argument applications into case-constr form"
              ::
              Data.Text.Text)
      MAlonzo.Code.VerifiedCompilation.Trace.C_caseReduceT_26
        -> coe
             ("Case-Constr and Case-Constant Cancellation" :: Data.Text.Text)
      MAlonzo.Code.VerifiedCompilation.Trace.C_letFloatOutT_28
        -> coe ("Float bindings outwards" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- CertifierReport.showUncertifiedOptTag
d_showUncertifiedOptTag_12 ::
  MAlonzo.Code.VerifiedCompilation.Trace.T_UncertifiedOptTag_4 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showUncertifiedOptTag_12 v0
  = case coe v0 of
      MAlonzo.Code.VerifiedCompilation.Trace.C_caseOfCaseT_6
        -> coe ("Case-of-Case" :: Data.Text.Text)
      MAlonzo.Code.VerifiedCompilation.Trace.C_constantFoldingT_8
        -> coe ("Constant Folding" :: Data.Text.Text)
      MAlonzo.Code.VerifiedCompilation.Trace.C_polyBuiltinT_10
        -> coe ("Hoist Polymorphic Builtins" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- CertifierReport.showTag
d_showTag_14 ::
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.VerifiedCompilation.Trace.T_UncertifiedOptTag_4
    MAlonzo.Code.VerifiedCompilation.Trace.T_CertifiedOptTag_12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showTag_14 v0
  = case coe v0 of
      MAlonzo.Code.Utils.C_inj'8321'_12 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (d_showUncertifiedOptTag_12 (coe v1))
             ("  \9888 (certifier unavailable)" :: Data.Text.Text)
      MAlonzo.Code.Utils.C_inj'8322'_14 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (d_showCertifiedOptTag_10 (coe v1)) ("  \9989" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- CertifierReport.numSites′
d_numSites'8242'_26 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_8 ->
  Integer
d_numSites'8242'_26 ~v0 v1 v2 = du_numSites'8242'_26 v1 v2
du_numSites'8242'_26 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_8 ->
  Integer
du_numSites'8242'_26 v0 v1
  = coe
      du_go_40 (coe v0) (coe v1) (coe (0 :: Integer)) (coe v0) (coe v1)
      (coe (0 :: Integer))
-- CertifierReport._.go
d_go_40 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Integer ->
  MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_8 ->
  Integer
d_go_40 ~v0 v1 v2 ~v3 v4 v5 v6 v7 v8
  = du_go_40 v1 v2 v4 v5 v6 v7 v8
du_go_40 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Integer ->
  MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_8 ->
  Integer
du_go_40 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_istranslation_88 v9
        -> coe addInt (coe (1 :: Integer)) (coe v5)
      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_match_94 v9
        -> coe
             du_go'7504'_50 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v9)
      _ -> MAlonzo.RTE.mazUnreachableError
-- CertifierReport._.goᵐ
d_go'7504'_50 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Integer ->
  MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_TransMatch_14 ->
  Integer
d_go'7504'_50 ~v0 v1 v2 ~v3 v4 v5 v6 v7 v8
  = du_go'7504'_50 v1 v2 v4 v5 v6 v7 v8
du_go'7504'_50 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Integer ->
  MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_TransMatch_14 ->
  Integer
du_go'7504'_50 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_var_22
        -> coe v5
      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_ƛ_28 v9
        -> case coe v3 of
             MAlonzo.Code.Untyped.C_ƛ_20 v10
               -> case coe v4 of
                    MAlonzo.Code.Untyped.C_ƛ_20 v11
                      -> coe
                           du_go_40 (coe v0) (coe v1)
                           (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v10) (coe v11)
                           (coe v5) (coe v9)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_app_38 v11 v12
        -> case coe v3 of
             MAlonzo.Code.Untyped.C__'183'__22 v13 v14
               -> case coe v4 of
                    MAlonzo.Code.Untyped.C__'183'__22 v15 v16
                      -> coe
                           du_go_40 (coe v0) (coe v1) (coe v2) (coe v14) (coe v16)
                           (coe
                              du_go_40 (coe v0) (coe v1) (coe v2) (coe v13) (coe v15) (coe v5)
                              (coe v11))
                           (coe v12)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_force_44 v9
        -> case coe v3 of
             MAlonzo.Code.Untyped.C_force_24 v10
               -> case coe v4 of
                    MAlonzo.Code.Untyped.C_force_24 v11
                      -> coe
                           du_go_40 (coe v0) (coe v1) (coe v2) (coe v10) (coe v11) (coe v5)
                           (coe v9)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_delay_50 v9
        -> case coe v3 of
             MAlonzo.Code.Untyped.C_delay_26 v10
               -> case coe v4 of
                    MAlonzo.Code.Untyped.C_delay_26 v11
                      -> coe
                           du_go_40 (coe v0) (coe v1) (coe v2) (coe v10) (coe v11) (coe v5)
                           (coe v9)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_con_54
        -> coe v5
      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_constr_62 v10
        -> case coe v3 of
             MAlonzo.Code.Untyped.C_constr_34 v11 v12
               -> case coe v4 of
                    MAlonzo.Code.Untyped.C_constr_34 v13 v14
                      -> coe
                           du_go'7510''695'_60 (coe v0) (coe v1) (coe v2) (coe v12) (coe v14)
                           (coe v5) (coe v10)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_case_72 v11 v12
        -> case coe v3 of
             MAlonzo.Code.Untyped.C_case_40 v13 v14
               -> case coe v4 of
                    MAlonzo.Code.Untyped.C_case_40 v15 v16
                      -> coe
                           du_go_40 (coe v0) (coe v1) (coe v2) (coe v13) (coe v15)
                           (coe
                              du_go'7510''695'_60 (coe v0) (coe v1) (coe v2) (coe v14) (coe v16)
                              (coe v5) (coe v11))
                           (coe v12)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_builtin_76
        -> coe v5
      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_error_78
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- CertifierReport._.goᵖʷ
d_go'7510''695'_60 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
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
d_go'7510''695'_60 ~v0 v1 v2 ~v3 v4 v5 v6 v7 v8
  = du_go'7510''695'_60 v1 v2 v4 v5 v6 v7 v8
du_go'7510''695'_60 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  Integer
du_go'7510''695'_60 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C_'91''93'_56
        -> coe v5
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v11 v12
        -> case coe v3 of
             (:) v13 v14
               -> case coe v4 of
                    (:) v15 v16
                      -> coe
                           du_go'7510''695'_60 (coe v0) (coe v1) (coe v2) (coe v14) (coe v16)
                           (coe
                              du_go_40 (coe v0) (coe v1) (coe v2) (coe v13) (coe v15) (coe v5)
                              (coe v11))
                           (coe v12)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- CertifierReport.numSitesInlineᵖʷ
d_numSitesInline'7510''695'_122 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  Integer
d_numSitesInline'7510''695'_122 v0 v1 v2 v3 v4
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
                              d_numSitesInline_140 (coe v0) (coe v1)
                              (coe MAlonzo.Code.VerifiedCompilation.UInline.C_'9633'_32)
                              (coe MAlonzo.Code.VerifiedCompilation.UInline.C_'9633'_32)
                              (coe MAlonzo.Code.VerifiedCompilation.UInline.C_'9633'_106)
                              (coe v11) (coe v13) (coe v9))
                           (coe
                              d_numSitesInline'7510''695'_122 (coe v0) (coe v1) (coe v12)
                              (coe v14) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- CertifierReport.numSitesInline
d_numSitesInline_140 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  MAlonzo.Code.VerifiedCompilation.UInline.T__'8605'_28 ->
  MAlonzo.Code.VerifiedCompilation.UInline.T__'8605'_28 ->
  MAlonzo.Code.VerifiedCompilation.UInline.T__'8829'__102 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.UInline.T_Inline_224 -> Integer
d_numSitesInline_140 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.VerifiedCompilation.UInline.C_'96'_230
        -> coe (0 :: Integer)
      MAlonzo.Code.VerifiedCompilation.UInline.C_'96''8595'_234 v14
        -> case coe v5 of
             MAlonzo.Code.Untyped.C_'96'_18 v15
               -> coe
                    addInt (coe (1 :: Integer))
                    (coe
                       d_numSitesInline_140 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v1 v15) (coe v6) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.VerifiedCompilation.UInline.C_ƛ'9633'_236 v11
        -> case coe v5 of
             MAlonzo.Code.Untyped.C_ƛ_20 v12
               -> case coe v6 of
                    MAlonzo.Code.Untyped.C_ƛ_20 v13
                      -> coe
                           d_numSitesInline_140 (coe addInt (coe (1 :: Integer)) (coe v0))
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
                                                d_numSitesInline_140
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
                                         d_numSitesInline_140
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
                              d_numSitesInline_140 (coe v0) (coe v1)
                              (coe MAlonzo.Code.VerifiedCompilation.UInline.C_'9633'_32)
                              (coe MAlonzo.Code.VerifiedCompilation.UInline.C_'9633'_32)
                              (coe MAlonzo.Code.VerifiedCompilation.UInline.C_'9633'_106)
                              (coe v19) (coe v21) (coe v17))
                           (coe
                              d_numSitesInline_140 (coe v0) (coe v1)
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
                    d_numSitesInline_140 (coe v0) (coe v1)
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
                           d_numSitesInline_140 (coe v0) (coe v1)
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
                           d_numSitesInline_140 (coe v0) (coe v1)
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
                           d_numSitesInline'7510''695'_122 (coe v0) (coe v1) (coe v17)
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
                              d_numSitesInline_140 (coe v0) (coe v1)
                              (coe MAlonzo.Code.VerifiedCompilation.UInline.C_'9633'_32)
                              (coe MAlonzo.Code.VerifiedCompilation.UInline.C_'9633'_32)
                              (coe MAlonzo.Code.VerifiedCompilation.UInline.C_'9633'_106)
                              (coe v18) (coe v20) (coe v16))
                           (coe
                              d_numSitesInline'7510''695'_122 (coe v0) (coe v1) (coe v19)
                              (coe v21) (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.VerifiedCompilation.UInline.C_error_292
        -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- CertifierReport.numSitesCaseReduce
d_numSitesCaseReduce_178 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.Relation.Binary.Modular.T_Fix_50 -> Integer
d_numSitesCaseReduce_178 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Untyped.Relation.Binary.Modular.C_fix_60 v7
        -> case coe v7 of
             MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inl_30 v11
               -> coe (1 :: Integer)
             MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38 v11
               -> case coe v11 of
                    MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inl_30 v15
                      -> case coe v15 of
                           MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inl_30 v19
                             -> coe seq (coe v19) (coe (0 :: Integer))
                           MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38 v19
                             -> case coe v19 of
                                  MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inl_30 v23
                                    -> case coe v23 of
                                         MAlonzo.Code.Untyped.Relation.Binary.Modular.C_ƛF_132 v27
                                           -> case coe v1 of
                                                MAlonzo.Code.Untyped.C_ƛ_20 v28
                                                  -> case coe v2 of
                                                       MAlonzo.Code.Untyped.C_ƛ_20 v29
                                                         -> coe
                                                              d_numSitesCaseReduce_178
                                                              (coe
                                                                 addInt (coe (1 :: Integer))
                                                                 (coe v0))
                                                              (coe v28) (coe v29) (coe v27)
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38 v23
                                    -> case coe v23 of
                                         MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inl_30 v27
                                           -> case coe v27 of
                                                MAlonzo.Code.Untyped.Relation.Binary.Modular.C__'183'F__150 v33 v34
                                                  -> case coe v1 of
                                                       MAlonzo.Code.Untyped.C__'183'__22 v35 v36
                                                         -> case coe v2 of
                                                              MAlonzo.Code.Untyped.C__'183'__22 v37 v38
                                                                -> coe
                                                                     addInt
                                                                     (coe
                                                                        d_numSitesCaseReduce_178
                                                                        (coe v0) (coe v35) (coe v37)
                                                                        (coe v33))
                                                                     (coe
                                                                        d_numSitesCaseReduce_178
                                                                        (coe v0) (coe v36) (coe v38)
                                                                        (coe v34))
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38 v27
                                           -> case coe v27 of
                                                MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inl_30 v31
                                                  -> case coe v31 of
                                                       MAlonzo.Code.Untyped.Relation.Binary.Modular.C_forceF_164 v35
                                                         -> case coe v1 of
                                                              MAlonzo.Code.Untyped.C_force_24 v36
                                                                -> case coe v2 of
                                                                     MAlonzo.Code.Untyped.C_force_24 v37
                                                                       -> coe
                                                                            d_numSitesCaseReduce_178
                                                                            (coe v0) (coe v36)
                                                                            (coe v37) (coe v35)
                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38 v31
                                                  -> case coe v31 of
                                                       MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inl_30 v35
                                                         -> case coe v35 of
                                                              MAlonzo.Code.Untyped.Relation.Binary.Modular.C_delayF_178 v39
                                                                -> case coe v1 of
                                                                     MAlonzo.Code.Untyped.C_delay_26 v40
                                                                       -> case coe v2 of
                                                                            MAlonzo.Code.Untyped.C_delay_26 v41
                                                                              -> coe
                                                                                   d_numSitesCaseReduce_178
                                                                                   (coe v0)
                                                                                   (coe v40)
                                                                                   (coe v41)
                                                                                   (coe v39)
                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38 v35
                                                         -> case coe v35 of
                                                              MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inl_30 v39
                                                                -> coe
                                                                     seq (coe v39)
                                                                     (coe (0 :: Integer))
                                                              MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38 v39
                                                                -> case coe v39 of
                                                                     MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inl_30 v43
                                                                       -> case coe v43 of
                                                                            MAlonzo.Code.Untyped.Relation.Binary.Modular.C_constrF_206 v48
                                                                              -> case coe v1 of
                                                                                   MAlonzo.Code.Untyped.C_constr_34 v49 v50
                                                                                     -> case coe
                                                                                               v2 of
                                                                                          MAlonzo.Code.Untyped.C_constr_34 v51 v52
                                                                                            -> coe
                                                                                                 d_numSitesCaseReduce'42'_186
                                                                                                 (coe
                                                                                                    v0)
                                                                                                 (coe
                                                                                                    v50)
                                                                                                 (coe
                                                                                                    v52)
                                                                                                 (coe
                                                                                                    v48)
                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                     MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38 v43
                                                                       -> case coe v43 of
                                                                            MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inl_30 v47
                                                                              -> case coe v47 of
                                                                                   MAlonzo.Code.Untyped.Relation.Binary.Modular.C_caseF_224 v53 v54
                                                                                     -> case coe
                                                                                               v1 of
                                                                                          MAlonzo.Code.Untyped.C_case_40 v55 v56
                                                                                            -> case coe
                                                                                                      v2 of
                                                                                                 MAlonzo.Code.Untyped.C_case_40 v57 v58
                                                                                                   -> coe
                                                                                                        addInt
                                                                                                        (coe
                                                                                                           d_numSitesCaseReduce'42'_186
                                                                                                           (coe
                                                                                                              v0)
                                                                                                           (coe
                                                                                                              v56)
                                                                                                           (coe
                                                                                                              v58)
                                                                                                           (coe
                                                                                                              v54))
                                                                                                        (coe
                                                                                                           d_numSitesCaseReduce_178
                                                                                                           (coe
                                                                                                              v0)
                                                                                                           (coe
                                                                                                              v55)
                                                                                                           (coe
                                                                                                              v57)
                                                                                                           (coe
                                                                                                              v53))
                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                            MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38 v47
                                                                              -> case coe v47 of
                                                                                   MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inl_30 v51
                                                                                     -> coe
                                                                                          seq
                                                                                          (coe v51)
                                                                                          (coe
                                                                                             (0 ::
                                                                                                Integer))
                                                                                   MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38 v51
                                                                                     -> case coe
                                                                                               v51 of
                                                                                          MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inl_30 v55
                                                                                            -> coe
                                                                                                 seq
                                                                                                 (coe
                                                                                                    v55)
                                                                                                 (coe
                                                                                                    (0 ::
                                                                                                       Integer))
                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38 v15
                      -> case coe v15 of
                           MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inl_30 v19
                             -> case coe v19 of
                                  MAlonzo.Code.Untyped.Relation.Binary.Modular.C_transF_80 v22 v24 v25
                                    -> coe
                                         addInt
                                         (coe
                                            d_numSitesCaseReduce_178 (coe v0) (coe v1) (coe v22)
                                            (coe v24))
                                         (coe
                                            d_numSitesCaseReduce_178 (coe v0) (coe v22) (coe v2)
                                            (coe v25))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38 v19
                             -> case coe v19 of
                                  MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inl_30 v23
                                    -> case coe v23 of
                                         MAlonzo.Code.Untyped.Relation.Binary.Modular.C_symF_94 v27
                                           -> coe
                                                d_numSitesCaseReduce_178 (coe v0) (coe v2) (coe v1)
                                                (coe v27)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38 v23
                                    -> coe seq (coe v23) (coe (0 :: Integer))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- CertifierReport.numSitesCaseReduce*
d_numSitesCaseReduce'42'_186 ::
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Untyped.Relation.Binary.Core.T_Pointwise_20 -> Integer
d_numSitesCaseReduce'42'_186 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Untyped.Relation.Binary.Core.C_'91''93'_26
        -> coe (0 :: Integer)
      MAlonzo.Code.Untyped.Relation.Binary.Core.C__'8759'__36 v8 v9
        -> case coe v1 of
             (:) v10 v11
               -> case coe v2 of
                    (:) v12 v13
                      -> coe
                           addInt
                           (coe
                              d_numSitesCaseReduce'42'_186 (coe v0) (coe v11) (coe v13) (coe v9))
                           (coe
                              d_numSitesCaseReduce_178 (coe v0) (coe v10) (coe v12) (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- CertifierReport.numSites
d_numSites_222 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Trace.T_CertifiedOptTag_12 ->
  AgdaAny -> Integer
d_numSites_222 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.VerifiedCompilation.Trace.C_floatDelayT_14
        -> coe du_numSites'8242'_26 v0 v1 v3
      MAlonzo.Code.VerifiedCompilation.Trace.C_forceDelayT_16
        -> coe du_numSites'8242'_26 v0 v1 v3
      MAlonzo.Code.VerifiedCompilation.Trace.C_forceCaseDelayT_18
        -> coe du_numSites'8242'_26 v0 v1 v3
      MAlonzo.Code.VerifiedCompilation.Trace.C_inlineT_20
        -> coe
             d_numSitesInline_140 (coe (0 :: Integer)) erased
             (coe MAlonzo.Code.VerifiedCompilation.UInline.C_'9633'_32)
             (coe MAlonzo.Code.VerifiedCompilation.UInline.C_'9633'_32)
             (coe MAlonzo.Code.VerifiedCompilation.UInline.C_'9633'_106)
             (coe v0) (coe v1) (coe v3)
      MAlonzo.Code.VerifiedCompilation.Trace.C_cseT_22
        -> coe du_numSites'8242'_26 v0 v1 v3
      MAlonzo.Code.VerifiedCompilation.Trace.C_applyToCaseT_24
        -> coe du_numSites'8242'_26 v0 v1 v3
      MAlonzo.Code.VerifiedCompilation.Trace.C_caseReduceT_26
        -> coe
             d_numSitesCaseReduce_178 (coe (0 :: Integer)) (coe v0) (coe v1)
             (coe
                MAlonzo.Code.VerifiedCompilation.UCaseReduce.du_sound_568
                (coe (0 :: Integer)) (coe v0))
      MAlonzo.Code.VerifiedCompilation.Trace.C_letFloatOutT_28
        -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- CertifierReport.showSites
d_showSites_248 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.VerifiedCompilation.Trace.T_UncertifiedOptTag_4
    MAlonzo.Code.VerifiedCompilation.Trace.T_CertifiedOptTag_12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showSites_248 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Utils.C_inj'8321'_12 v4 -> coe ("" :: Data.Text.Text)
      MAlonzo.Code.Utils.C_inj'8322'_14 v4
        -> coe
             d_'8649'__2
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("Optimization sites: " :: Data.Text.Text)
                (coe
                   MAlonzo.Code.Data.Nat.Show.d_show_56
                   (d_numSites_222 (coe v0) (coe v1) (coe v4) (coe v3))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- CertifierReport.termSize
d_termSize_256 ::
  Integer -> MAlonzo.Code.Untyped.T__'8866'_14 -> Integer
d_termSize_256 v0 v1
  = case coe v1 of
      MAlonzo.Code.Untyped.C_'96'_18 v2 -> coe (1 :: Integer)
      MAlonzo.Code.Untyped.C_ƛ_20 v2
        -> coe
             addInt (coe (1 :: Integer))
             (coe
                d_termSize_256 (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v2))
      MAlonzo.Code.Untyped.C__'183'__22 v2 v3
        -> coe
             addInt
             (coe
                addInt (coe (1 :: Integer)) (coe d_termSize_256 (coe v0) (coe v2)))
             (coe d_termSize_256 (coe v0) (coe v3))
      MAlonzo.Code.Untyped.C_force_24 v2
        -> coe
             addInt (coe (1 :: Integer)) (coe d_termSize_256 (coe v0) (coe v2))
      MAlonzo.Code.Untyped.C_delay_26 v2
        -> coe
             addInt (coe (1 :: Integer)) (coe d_termSize_256 (coe v0) (coe v2))
      MAlonzo.Code.Untyped.C_con_28 v2 -> coe (1 :: Integer)
      MAlonzo.Code.Untyped.C_constr_34 v2 v3
        -> coe
             addInt (coe (1 :: Integer))
             (coe d_termSize'7510''695'_260 (coe v0) (coe v3))
      MAlonzo.Code.Untyped.C_case_40 v2 v3
        -> coe
             addInt
             (coe
                addInt (coe (1 :: Integer))
                (coe d_termSize'7510''695'_260 (coe v0) (coe v3)))
             (coe d_termSize_256 (coe v0) (coe v2))
      MAlonzo.Code.Untyped.C_builtin_44 v2 -> coe (1 :: Integer)
      MAlonzo.Code.Untyped.C_error_46 -> coe (1 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- CertifierReport.termSizeᵖʷ
d_termSize'7510''695'_260 ::
  Integer -> [MAlonzo.Code.Untyped.T__'8866'_14] -> Integer
d_termSize'7510''695'_260 v0 v1
  = case coe v1 of
      [] -> coe (0 :: Integer)
      (:) v2 v3
        -> coe
             addInt (coe d_termSize'7510''695'_260 (coe v0) (coe v3))
             (coe d_termSize_256 (coe v0) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- CertifierReport.showEvalResult
d_showEvalResult_282 ::
  MAlonzo.Code.VerifiedCompilation.Trace.T_EvalResult_122 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showEvalResult_282 v0
  = case coe v0 of
      MAlonzo.Code.VerifiedCompilation.Trace.C_success_124 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (d_'8649'__2 (coe ("Execution Cost: CPU = " :: Data.Text.Text)))
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", MEM = " :: Data.Text.Text)
                   (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)))
      MAlonzo.Code.VerifiedCompilation.Trace.C_failure_126 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (d_'8649'__2 (coe ("Evaluation FAILED: " :: Data.Text.Text)))
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20 d_nl_6
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_'8649'__2 (coe ("Execution Cost: CPU = " :: Data.Text.Text)))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (", MEM = " :: Data.Text.Text)
                            (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v3))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- CertifierReport.showCostPair
d_showCostPair_294 ::
  [MAlonzo.Code.VerifiedCompilation.Trace.T_EvalResult_122] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showCostPair_294 v0
  = let v1 = "" :: Data.Text.Text in
    coe
      (case coe v0 of
         (:) v2 v3
           -> case coe v3 of
                (:) v4 v5
                  -> coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       (d_showEvalResult_282 (coe v2))
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          (" (before)" :: Data.Text.Text)
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20 d_nl_6
                             (coe
                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                (d_showEvalResult_282 (coe v4)) (" (after)" :: Data.Text.Text))))
                _ -> coe v1
         _ -> coe v1)
-- CertifierReport.tail
d_tail_302 :: () -> [AgdaAny] -> [AgdaAny]
d_tail_302 ~v0 v1 = du_tail_302 v1
du_tail_302 :: [AgdaAny] -> [AgdaAny]
du_tail_302 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- CertifierReport.reportPasses
d_reportPasses_312 ::
  Integer ->
  MAlonzo.Code.VerifiedCompilation.Trace.T_NonEmptySep_90
    (MAlonzo.Code.Utils.T__'215'__436
       (MAlonzo.Code.Utils.T_Either_6
          MAlonzo.Code.VerifiedCompilation.Trace.T_UncertifiedOptTag_4
          MAlonzo.Code.VerifiedCompilation.Trace.T_CertifiedOptTag_12)
       MAlonzo.Code.VerifiedCompilation.Trace.T_Hints_80)
    MAlonzo.Code.Untyped.T__'8866'_14 ->
  AgdaAny ->
  [MAlonzo.Code.VerifiedCompilation.Trace.T_EvalResult_122] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_reportPasses_312 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.VerifiedCompilation.Trace.C_cons_96 v4 v5 v6
        -> case coe v5 of
             MAlonzo.Code.Utils.C__'44'__450 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Utils.C__'44'__450 v9 v10
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20 d_hl_8
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              ("Pass " :: Data.Text.Text)
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                 (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v0)
                                 (coe
                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                    (": " :: Data.Text.Text)
                                    (coe
                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                       (d_showTag_14 (coe v7))
                                       (coe
                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20 d_hl_8
                                          (coe
                                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                             (d_'8649'__2
                                                (coe ("Program Size: " :: Data.Text.Text)))
                                             (coe
                                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                (coe
                                                   MAlonzo.Code.Data.Nat.Show.d_show_56
                                                   (d_termSize_256 (coe (0 :: Integer)) (coe v4)))
                                                (coe
                                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                   (" (before)" :: Data.Text.Text)
                                                   (coe
                                                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                      d_nl_6
                                                      (coe
                                                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                         (d_'8649'__2
                                                            (coe
                                                               ("Program Size: "
                                                                ::
                                                                Data.Text.Text)))
                                                         (coe
                                                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                            (coe
                                                               MAlonzo.Code.Data.Nat.Show.d_show_56
                                                               (d_termSize_256
                                                                  (coe (0 :: Integer))
                                                                  (coe
                                                                     MAlonzo.Code.VerifiedCompilation.Trace.d_head_112
                                                                     (coe v6))))
                                                            (coe
                                                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                               (" (after)" :: Data.Text.Text)
                                                               (coe
                                                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                  d_nl_6
                                                                  (coe
                                                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                     (d_showCostPair_294 (coe v3))
                                                                     (coe
                                                                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                        d_nl_6
                                                                        (coe
                                                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                           (d_showSites_248
                                                                              (coe v4)
                                                                              (coe
                                                                                 MAlonzo.Code.VerifiedCompilation.Trace.d_head_112
                                                                                 (coe v6))
                                                                              (coe v7) (coe v9))
                                                                           (coe
                                                                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                              d_nl_6
                                                                              (d_reportPasses_312
                                                                                 (coe
                                                                                    addInt
                                                                                    (coe
                                                                                       (1 ::
                                                                                          Integer))
                                                                                    (coe v0))
                                                                                 (coe v6) (coe v10)
                                                                                 (coe
                                                                                    du_tail_302
                                                                                    (coe
                                                                                       v3))))))))))))))))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.VerifiedCompilation.Trace.C_singleton_98 v4
        -> coe ("" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- CertifierReport.reportFailure
d_reportFailure_328 ::
  MAlonzo.Code.VerifiedCompilation.T_Error_2 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_reportFailure_328 v0
  = case coe v0 of
      MAlonzo.Code.VerifiedCompilation.C_emptyDump_4
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20 d_hl_8
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("Empty trace from the compiler  \10060 FAILED" :: Data.Text.Text)
                d_hl_8)
      MAlonzo.Code.VerifiedCompilation.C_illScoped_6
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20 d_hl_8
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("Trace from compiler contained ill-scoped terms  \10060 FAILED"
                 ::
                 Data.Text.Text)
                d_hl_8)
      MAlonzo.Code.VerifiedCompilation.C_counterExample_8 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20 d_hl_8
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("Pass " :: Data.Text.Text)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (d_showTag_14 (coe v1))
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("  \10060 FAILED" :: Data.Text.Text) d_hl_8)))
      MAlonzo.Code.VerifiedCompilation.C_abort_10 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20 d_hl_8
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("Pass " :: Data.Text.Text)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (d_showTag_14 (coe v1))
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("  \10060 FAILED" :: Data.Text.Text) d_hl_8)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- CertifierReport.makeReport
d_makeReport_334 ::
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.VerifiedCompilation.T_Error_2
    MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.VerifiedCompilation.Trace.T_EvalResult_122] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_makeReport_334 v0 v1
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("UPLC OPTIMIZATION: CERTIFIER REPORT" :: Data.Text.Text)
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20 d_nl_6
         (coe
            MAlonzo.Code.Utils.du_either_22 (coe v0) (coe d_reportFailure_328)
            (coe
               (\ v2 ->
                  case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                      -> coe
                           d_reportPasses_312 (coe (1 :: Integer)) (coe v3) (coe v4) (coe v1)
                    _ -> MAlonzo.RTE.mazUnreachableError))))
