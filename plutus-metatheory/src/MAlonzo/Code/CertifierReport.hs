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
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Untyped
import qualified MAlonzo.Code.Utils
import qualified MAlonzo.Code.VerifiedCompilation
import qualified MAlonzo.Code.VerifiedCompilation.Certificate
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
      ("\n\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\9472\n"
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
-- CertifierReport.numSites
d_numSites_114 ::
  Integer ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.T_Transformation_2 ->
  Maybe Integer
d_numSites_114 v0 ~v1 v2 v3 v4 = du_numSites_114 v0 v2 v3 v4
du_numSites_114 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.T_Transformation_2 ->
  Maybe Integer
du_numSites_114 v0 v1 v2 v3
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
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.VerifiedCompilation.C_isCaseReduce_40 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe du_numSites'8242'_20 v0 v1 v2 v7)
      MAlonzo.Code.VerifiedCompilation.C_forceCaseDelayNotImplemented_48
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.VerifiedCompilation.C_cocNotImplemented_56
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- CertifierReport.showSites
d_showSites_132 ::
  Integer ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.T_Transformation_2 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showSites_132 v0 ~v1 v2 v3 v4 = du_showSites_132 v0 v2 v3 v4
du_showSites_132 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.T_Transformation_2 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_showSites_132 v0 v1 v2 v3
  = let v4
          = coe du_numSites_114 (coe v0) (coe v1) (coe v2) (coe v3) in
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
d_termSize_148 ::
  Integer -> MAlonzo.Code.Untyped.T__'8866'_14 -> Integer
d_termSize_148 v0 v1
  = case coe v1 of
      MAlonzo.Code.Untyped.C_'96'_18 v2 -> coe (1 :: Integer)
      MAlonzo.Code.Untyped.C_ƛ_20 v2
        -> coe
             addInt (coe (1 :: Integer))
             (coe
                d_termSize_148 (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v2))
      MAlonzo.Code.Untyped.C__'183'__22 v2 v3
        -> coe
             addInt
             (coe
                addInt (coe (1 :: Integer)) (coe d_termSize_148 (coe v0) (coe v2)))
             (coe d_termSize_148 (coe v0) (coe v3))
      MAlonzo.Code.Untyped.C_force_24 v2
        -> coe
             addInt (coe (1 :: Integer)) (coe d_termSize_148 (coe v0) (coe v2))
      MAlonzo.Code.Untyped.C_delay_26 v2
        -> coe
             addInt (coe (1 :: Integer)) (coe d_termSize_148 (coe v0) (coe v2))
      MAlonzo.Code.Untyped.C_con_28 v2 -> coe (1 :: Integer)
      MAlonzo.Code.Untyped.C_constr_34 v2 v3
        -> coe
             addInt (coe (1 :: Integer))
             (coe d_termSize'7510''695'_152 (coe v0) (coe v3))
      MAlonzo.Code.Untyped.C_case_40 v2 v3
        -> coe
             addInt
             (coe
                addInt (coe (1 :: Integer))
                (coe d_termSize'7510''695'_152 (coe v0) (coe v3)))
             (coe d_termSize_148 (coe v0) (coe v2))
      MAlonzo.Code.Untyped.C_builtin_44 v2 -> coe (1 :: Integer)
      MAlonzo.Code.Untyped.C_error_46 -> coe (1 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- CertifierReport.termSizeᵖʷ
d_termSize'7510''695'_152 ::
  Integer -> [MAlonzo.Code.Untyped.T__'8866'_14] -> Integer
d_termSize'7510''695'_152 v0 v1
  = case coe v1 of
      [] -> coe (0 :: Integer)
      (:) v2 v3
        -> coe
             addInt (coe d_termSize'7510''695'_152 (coe v0) (coe v3))
             (coe d_termSize_148 (coe v0) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- CertifierReport.reportPasses
d_reportPasses_182 ::
  Integer ->
  MAlonzo.Code.Utils.T_List_414
    (MAlonzo.Code.Utils.T__'215'__396
       MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4
       (MAlonzo.Code.Utils.T__'215'__396
          MAlonzo.Code.VerifiedCompilation.Certificate.T_Hints_46
          (MAlonzo.Code.Utils.T__'215'__396
             MAlonzo.Code.Untyped.T__'8866'_14
             MAlonzo.Code.Untyped.T__'8866'_14))) ->
  Integer ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_CertResult_60 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_reportPasses_182 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_66 v4
        -> case coe v4 of
             MAlonzo.Code.VerifiedCompilation.C_empty_64
               -> coe ("" :: Data.Text.Text)
             MAlonzo.Code.VerifiedCompilation.C_cons_78 v11 v12
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
                                                                           (d_termSize_148
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
                                                                                    (d_termSize_148
                                                                                       (coe v0)
                                                                                       (coe v20)))
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                                    d_nl_6
                                                                                    (coe
                                                                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                                       (coe
                                                                                          du_showSites_132
                                                                                          (coe v0)
                                                                                          (coe v19)
                                                                                          (coe v20)
                                                                                          (coe v11))
                                                                                       (coe
                                                                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                                          d_nl_6
                                                                                          (d_reportPasses_182
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
                                                                                                MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_66
                                                                                                (coe
                                                                                                   v12)))))))))))))))))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_74 v7 v8 v9
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
      MAlonzo.Code.VerifiedCompilation.Certificate.C_abort_80 v6 v7 v8
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
d_makeReport_210 ::
  Integer ->
  MAlonzo.Code.Utils.T_List_414
    (MAlonzo.Code.Utils.T__'215'__396
       MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4
       (MAlonzo.Code.Utils.T__'215'__396
          MAlonzo.Code.VerifiedCompilation.Certificate.T_Hints_46
          (MAlonzo.Code.Utils.T__'215'__396
             MAlonzo.Code.Untyped.T__'8866'_14
             MAlonzo.Code.Untyped.T__'8866'_14))) ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_CertResult_60 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_makeReport_210 v0 v1 v2
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("UPLC OPTIMIZATION: CERTIFIER REPORT" :: Data.Text.Text)
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20 d_nl_6
         (d_reportPasses_182
            (coe v0) (coe v1) (coe (1 :: Integer)) (coe v2)))
