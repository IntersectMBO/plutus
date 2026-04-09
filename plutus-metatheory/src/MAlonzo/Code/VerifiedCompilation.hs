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
{-# LANGUAGE GADTs #-}

module MAlonzo.Code.VerifiedCompilation where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.RawU
import qualified MAlonzo.Code.Untyped
import qualified MAlonzo.Code.Utils
import qualified MAlonzo.Code.VerifiedCompilation.Certificate
import qualified MAlonzo.Code.VerifiedCompilation.NotImplemented
import qualified MAlonzo.Code.VerifiedCompilation.Trace
import qualified MAlonzo.Code.VerifiedCompilation.UApplyToCase
import qualified MAlonzo.Code.VerifiedCompilation.UCSE
import qualified MAlonzo.Code.VerifiedCompilation.UCaseReduce
import qualified MAlonzo.Code.VerifiedCompilation.UFloatDelay
import qualified MAlonzo.Code.VerifiedCompilation.UForceCaseDelay
import qualified MAlonzo.Code.VerifiedCompilation.UForceDelay
import qualified MAlonzo.Code.VerifiedCompilation.UInline

import UntypedPlutusCore.Transform.Certify.Trace
-- VerifiedCompilation.Error
d_Error_2 = ()
data T_Error_2
  = C_emptyDump_4 | C_illScoped_6 |
    C_counterExample_8 MAlonzo.Code.VerifiedCompilation.Trace.T_SimplifierTag_4 |
    C_abort_10 MAlonzo.Code.VerifiedCompilation.Trace.T_SimplifierTag_4
-- VerifiedCompilation.mRelationOf
d_mRelationOf_12 ::
  MAlonzo.Code.VerifiedCompilation.Trace.T_SimplifierTag_4 ->
  Maybe
    (MAlonzo.Code.Untyped.T__'8866'_14 ->
     MAlonzo.Code.Untyped.T__'8866'_14 -> ())
d_mRelationOf_12 v0
  = case coe v0 of
      MAlonzo.Code.VerifiedCompilation.Trace.C_floatDelayT_6
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased
      MAlonzo.Code.VerifiedCompilation.Trace.C_forceDelayT_8
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased
      MAlonzo.Code.VerifiedCompilation.Trace.C_forceCaseDelayT_10
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased
      MAlonzo.Code.VerifiedCompilation.Trace.C_caseOfCaseT_12
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.VerifiedCompilation.Trace.C_caseReduceT_14
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased
      MAlonzo.Code.VerifiedCompilation.Trace.C_inlineT_16
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased
      MAlonzo.Code.VerifiedCompilation.Trace.C_cseT_18
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased
      MAlonzo.Code.VerifiedCompilation.Trace.C_applyToCaseT_20
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased
      MAlonzo.Code.VerifiedCompilation.Trace.C_unknown_22
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.RelationOf
d_RelationOf_14 ::
  MAlonzo.Code.VerifiedCompilation.Trace.T_SimplifierTag_4 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> ()
d_RelationOf_14 = erased
-- VerifiedCompilation.hasRelation
d_hasRelation_16 ::
  MAlonzo.Code.VerifiedCompilation.Trace.T_SimplifierTag_4 -> Bool
d_hasRelation_16 v0
  = coe
      MAlonzo.Code.Data.Maybe.Base.du_is'45'just_20
      (coe d_mRelationOf_12 (coe v0))
-- VerifiedCompilation.Yes
d_Yes_18 = ()
type T_Yes_18 = Yes
pattern C_yes_20 = Yes
check_yes_20 :: T_Yes_18
check_yes_20 = Yes
cover_Yes_18 :: Yes -> ()
cover_Yes_18 x
  = case x of
      Yes -> ()
-- VerifiedCompilation.No
d_No_22 = ()
type T_No_22 = No
pattern C_no_24 = No
check_no_24 :: T_No_22
check_no_24 = No
cover_No_22 :: No -> ()
cover_No_22 x
  = case x of
      No -> ()
-- VerifiedCompilation.CertifierImplements
d_CertifierImplements_26 a0 = ()
type T_CertifierImplements_26 = CertifierImplements
pattern C_certFloatDelay_28 = CertFloatDelay
pattern C_certForceDelay_30 = CertForceDelay
pattern C_certCaseOfCase_32 = CertCaseOfCase
pattern C_certCaseReduce_34 = CertCaseReduce
pattern C_certInline_36 = CertInline
pattern C_certCSE_38 = CertCSE
pattern C_certApplyToCase_40 = CertApplyToCase
pattern C_certUnknown_42 = CertUnknown
check_certFloatDelay_28 :: T_CertifierImplements_26 T_Yes_18
check_certFloatDelay_28 = CertFloatDelay
check_certForceDelay_30 :: T_CertifierImplements_26 T_Yes_18
check_certForceDelay_30 = CertForceDelay
check_certCaseOfCase_32 :: T_CertifierImplements_26 T_No_22
check_certCaseOfCase_32 = CertCaseOfCase
check_certCaseReduce_34 :: T_CertifierImplements_26 T_Yes_18
check_certCaseReduce_34 = CertCaseReduce
check_certInline_36 :: T_CertifierImplements_26 T_Yes_18
check_certInline_36 = CertInline
check_certCSE_38 :: T_CertifierImplements_26 T_Yes_18
check_certCSE_38 = CertCSE
check_certApplyToCase_40 :: T_CertifierImplements_26 T_Yes_18
check_certApplyToCase_40 = CertApplyToCase
check_certUnknown_42 :: T_CertifierImplements_26 T_No_22
check_certUnknown_42 = CertUnknown
cover_CertifierImplements_26 :: CertifierImplements a1 -> ()
cover_CertifierImplements_26 x
  = case x of
      CertFloatDelay -> ()
      CertForceDelay -> ()
      CertCaseOfCase -> ()
      CertCaseReduce -> ()
      CertInline -> ()
      CertCSE -> ()
      CertApplyToCase -> ()
      CertUnknown -> ()
-- VerifiedCompilation.f
d_f_46 :: () -> T_CertifierImplements_26 AgdaAny -> AgdaAny
d_f_46 ~v0 v1 = du_f_46 v1
du_f_46 :: T_CertifierImplements_26 AgdaAny -> AgdaAny
du_f_46 v0
  = case coe v0 of
      C_certFloatDelay_28 -> coe C_yes_20
      C_certForceDelay_30 -> coe C_yes_20
      C_certCaseOfCase_32 -> coe C_no_24
      C_certCaseReduce_34 -> coe C_yes_20
      C_certInline_36 -> coe C_yes_20
      C_certCSE_38 -> coe C_yes_20
      C_certApplyToCase_40 -> coe C_yes_20
      C_certUnknown_42 -> coe C_no_24
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.certifyPass
d_certifyPass_54 ::
  MAlonzo.Code.VerifiedCompilation.Trace.T_SimplifierTag_4 ->
  MAlonzo.Code.VerifiedCompilation.Trace.T_Hints_52 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_CertResult_12
d_certifyPass_54 v0 v1
  = case coe v0 of
      MAlonzo.Code.VerifiedCompilation.Trace.C_floatDelayT_6
        -> coe
             MAlonzo.Code.VerifiedCompilation.Certificate.du_decider_192
             (coe
                MAlonzo.Code.VerifiedCompilation.UFloatDelay.d_isFloatDelay'63'_488
                (coe (0 :: Integer)))
      MAlonzo.Code.VerifiedCompilation.Trace.C_forceDelayT_8
        -> coe
             MAlonzo.Code.VerifiedCompilation.Certificate.du_decider_192
             (coe
                MAlonzo.Code.VerifiedCompilation.UForceDelay.d_isForceDelay'63'_178
                (coe (0 :: Integer)))
      MAlonzo.Code.VerifiedCompilation.Trace.C_forceCaseDelayT_10
        -> coe
             MAlonzo.Code.VerifiedCompilation.Certificate.du_decider_192
             (coe
                MAlonzo.Code.VerifiedCompilation.UForceCaseDelay.d_isForceCaseDelay'63'_94
                (coe (0 :: Integer)))
      MAlonzo.Code.VerifiedCompilation.Trace.C_caseOfCaseT_12
        -> coe
             (\ v2 v3 ->
                coe
                  MAlonzo.Code.VerifiedCompilation.NotImplemented.du_certNotImplemented_22)
      MAlonzo.Code.VerifiedCompilation.Trace.C_caseReduceT_14
        -> coe
             MAlonzo.Code.VerifiedCompilation.Certificate.du_decider_192
             (coe
                MAlonzo.Code.VerifiedCompilation.UCaseReduce.d_isCaseReduce'63'_26
                (coe (0 :: Integer)))
      MAlonzo.Code.VerifiedCompilation.Trace.C_inlineT_16
        -> case coe v1 of
             MAlonzo.Code.VerifiedCompilation.Trace.C_inline_54 v2
               -> coe
                    MAlonzo.Code.VerifiedCompilation.Certificate.du_checker_156
                    (coe
                       MAlonzo.Code.VerifiedCompilation.UInline.d_top'45'check_718
                       (coe v2))
             MAlonzo.Code.VerifiedCompilation.Trace.C_none_56
               -> coe
                    MAlonzo.Code.VerifiedCompilation.Certificate.C_abort_32 (coe v0)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.VerifiedCompilation.Trace.C_cseT_18
        -> coe
             MAlonzo.Code.VerifiedCompilation.Certificate.du_decider_192
             (coe
                MAlonzo.Code.VerifiedCompilation.UCSE.d_isUntypedCSE'63'_26
                (coe (0 :: Integer)))
      MAlonzo.Code.VerifiedCompilation.Trace.C_applyToCaseT_20
        -> coe
             MAlonzo.Code.VerifiedCompilation.Certificate.du_decider_192
             (coe
                MAlonzo.Code.VerifiedCompilation.UApplyToCase.d_a2c'63''7580''7580'_24
                (coe (0 :: Integer)))
      MAlonzo.Code.VerifiedCompilation.Trace.C_unknown_22
        -> coe
             (\ v2 v3 ->
                coe
                  MAlonzo.Code.VerifiedCompilation.NotImplemented.du_certNotImplemented_22)
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.Certificate
d_Certificate_62 ::
  MAlonzo.Code.VerifiedCompilation.Trace.T_Trace_60 -> ()
d_Certificate_62 = erased
-- VerifiedCompilation.certify
d_certify_74 ::
  MAlonzo.Code.VerifiedCompilation.Trace.T_Trace_60 ->
  MAlonzo.Code.Utils.T_Either_6 T_Error_2 AgdaAny
d_certify_74 v0
  = case coe v0 of
      MAlonzo.Code.VerifiedCompilation.Trace.C_step_64 v1 v2 v3 v4
        -> let v5
                 = coe
                     d_certifyPass_54 v1 v2 v3
                     (MAlonzo.Code.VerifiedCompilation.Trace.d_head_70 (coe v4)) in
           coe
             (case coe v5 of
                MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_18 v6
                  -> coe
                       MAlonzo.Code.Utils.du_eitherBind_54 (coe d_certify_74 (coe v4))
                       (coe
                          (\ v7 ->
                             coe
                               MAlonzo.Code.Utils.C_inj'8322'_14
                               (coe MAlonzo.Code.Utils.C__'44'__442 (coe v6) (coe v7))))
                MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_26 v9 v10 v11
                  -> coe
                       MAlonzo.Code.Utils.C_inj'8321'_12 (coe C_counterExample_8 (coe v9))
                MAlonzo.Code.VerifiedCompilation.Certificate.C_abort_32 v8 v9 v10
                  -> coe MAlonzo.Code.Utils.C_inj'8321'_12 (coe C_abort_10 (coe v8))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.VerifiedCompilation.Trace.C_done_66 v1
        -> coe
             MAlonzo.Code.Utils.C_inj'8322'_14
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.cert
d_cert_124 ::
  MAlonzo.Code.VerifiedCompilation.Trace.T_Trace_60 ->
  MAlonzo.Code.Utils.T_Either_6 T_Error_2 AgdaAny ->
  AgdaAny -> AgdaAny
d_cert_124 ~v0 v1 v2 = du_cert_124 v1 v2
du_cert_124 ::
  MAlonzo.Code.Utils.T_Either_6 T_Error_2 AgdaAny ->
  AgdaAny -> AgdaAny
du_cert_124 v0 v1
  = case coe v0 of
      MAlonzo.Code.Utils.C_inj'8322'_14 v2 -> coe seq (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.checkScope
d_checkScope_128 ::
  MAlonzo.Code.RawU.T_Untyped_208 ->
  Maybe MAlonzo.Code.Untyped.T__'8866'_14
d_checkScope_128 v0
  = coe
      MAlonzo.Code.Utils.du_eitherToMaybe_104
      (coe MAlonzo.Code.Untyped.d_scopeCheckU0_276 (coe v0))
-- VerifiedCompilation.checkScopeᵗ
d_checkScope'7511'_130 ::
  MAlonzo.Code.VerifiedCompilation.Trace.T_Trace_60 ->
  Maybe MAlonzo.Code.VerifiedCompilation.Trace.T_Trace_60
d_checkScope'7511'_130 v0
  = case coe v0 of
      MAlonzo.Code.VerifiedCompilation.Trace.C_step_64 v1 v2 v3 v4
        -> coe
             MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
             (coe d_checkScope_128 (coe v3))
             (coe
                (\ v5 ->
                   coe
                     MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                     (coe d_checkScope'7511'_130 (coe v4))
                     (coe
                        (\ v6 ->
                           coe
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                             (coe
                                MAlonzo.Code.VerifiedCompilation.Trace.C_step_64 (coe v1) (coe v2)
                                (coe v5) (coe v6))))))
      MAlonzo.Code.VerifiedCompilation.Trace.C_done_66 v1
        -> coe
             MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
             (coe d_checkScope_128 (coe v1))
             (coe
                (\ v2 ->
                   coe
                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                     (coe MAlonzo.Code.VerifiedCompilation.Trace.C_done_66 (coe v2))))
      _ -> MAlonzo.RTE.mazUnreachableError
