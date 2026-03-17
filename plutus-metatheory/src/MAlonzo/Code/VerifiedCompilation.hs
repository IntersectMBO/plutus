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
import qualified MAlonzo.Code.VerifiedCompilation.UForceDelay
import qualified MAlonzo.Code.VerifiedCompilation.UInline

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
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
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
-- VerifiedCompilation.certifyPass
d_certifyPass_24 ::
  MAlonzo.Code.VerifiedCompilation.Trace.T_SimplifierTag_4 ->
  MAlonzo.Code.VerifiedCompilation.Trace.T_Hints_52 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_CertResult_12
d_certifyPass_24 v0 v1
  = case coe v0 of
      MAlonzo.Code.VerifiedCompilation.Trace.C_floatDelayT_6
        -> coe
             MAlonzo.Code.VerifiedCompilation.Certificate.du_decider_184
             (coe
                MAlonzo.Code.VerifiedCompilation.UFloatDelay.d_isFloatDelay'63'_488
                (coe (0 :: Integer)))
      MAlonzo.Code.VerifiedCompilation.Trace.C_forceDelayT_8
        -> coe
             MAlonzo.Code.VerifiedCompilation.Certificate.du_decider_184
             (coe
                MAlonzo.Code.VerifiedCompilation.UForceDelay.d_isForceDelay'63'_178
                (coe (0 :: Integer)))
      MAlonzo.Code.VerifiedCompilation.Trace.C_forceCaseDelayT_10
        -> coe
             (\ v2 v3 ->
                coe
                  MAlonzo.Code.VerifiedCompilation.NotImplemented.du_certNotImplemented_22)
      MAlonzo.Code.VerifiedCompilation.Trace.C_caseOfCaseT_12
        -> coe
             (\ v2 v3 ->
                coe
                  MAlonzo.Code.VerifiedCompilation.NotImplemented.du_certNotImplemented_22)
      MAlonzo.Code.VerifiedCompilation.Trace.C_caseReduceT_14
        -> coe
             MAlonzo.Code.VerifiedCompilation.Certificate.du_decider_184
             (coe
                MAlonzo.Code.VerifiedCompilation.UCaseReduce.d_isCaseReduce'63'_26
                (coe (0 :: Integer)))
      MAlonzo.Code.VerifiedCompilation.Trace.C_inlineT_16
        -> case coe v1 of
             MAlonzo.Code.VerifiedCompilation.Trace.C_inline_54 v2
               -> coe
                    MAlonzo.Code.VerifiedCompilation.Certificate.du_checker_148
                    (coe
                       MAlonzo.Code.VerifiedCompilation.UInline.d_top'45'check_718
                       (coe v2))
             MAlonzo.Code.VerifiedCompilation.Trace.C_none_56
               -> coe
                    MAlonzo.Code.VerifiedCompilation.Certificate.C_abort_32 (coe v0)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.VerifiedCompilation.Trace.C_cseT_18
        -> coe
             MAlonzo.Code.VerifiedCompilation.Certificate.du_decider_184
             (coe
                MAlonzo.Code.VerifiedCompilation.UCSE.d_isUntypedCSE'63'_26
                (coe (0 :: Integer)))
      MAlonzo.Code.VerifiedCompilation.Trace.C_applyToCaseT_20
        -> coe
             MAlonzo.Code.VerifiedCompilation.Certificate.du_decider_184
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
d_Certificate_32 ::
  MAlonzo.Code.VerifiedCompilation.Trace.T_Trace_60 -> ()
d_Certificate_32 = erased
-- VerifiedCompilation.certify
d_certify_44 ::
  MAlonzo.Code.VerifiedCompilation.Trace.T_Trace_60 ->
  MAlonzo.Code.Utils.T_Either_6 T_Error_2 AgdaAny
d_certify_44 v0
  = case coe v0 of
      MAlonzo.Code.VerifiedCompilation.Trace.C_step_64 v1 v2 v3 v4
        -> let v5
                 = coe
                     d_certifyPass_24 v1 v2 v3
                     (MAlonzo.Code.VerifiedCompilation.Trace.d_head_70 (coe v4)) in
           coe
             (case coe v5 of
                MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_18 v6
                  -> coe
                       MAlonzo.Code.Utils.du_eitherBind_54 (coe d_certify_44 (coe v4))
                       (coe
                          (\ v7 ->
                             coe
                               MAlonzo.Code.Utils.C_inj'8322'_14
                               (coe MAlonzo.Code.Utils.C__'44'__440 (coe v6) (coe v7))))
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
d_cert_94 ::
  MAlonzo.Code.VerifiedCompilation.Trace.T_Trace_60 ->
  MAlonzo.Code.Utils.T_Either_6 T_Error_2 AgdaAny ->
  AgdaAny -> AgdaAny
d_cert_94 ~v0 v1 v2 = du_cert_94 v1 v2
du_cert_94 ::
  MAlonzo.Code.Utils.T_Either_6 T_Error_2 AgdaAny ->
  AgdaAny -> AgdaAny
du_cert_94 v0 v1
  = case coe v0 of
      MAlonzo.Code.Utils.C_inj'8322'_14 v2 -> coe seq (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.checkScope
d_checkScope_98 ::
  MAlonzo.Code.RawU.T_Untyped_208 ->
  Maybe MAlonzo.Code.Untyped.T__'8866'_14
d_checkScope_98 v0
  = coe
      MAlonzo.Code.Utils.du_eitherToMaybe_104
      (coe MAlonzo.Code.Untyped.d_scopeCheckU0_276 (coe v0))
-- VerifiedCompilation.checkScopeᵗ
d_checkScope'7511'_100 ::
  MAlonzo.Code.VerifiedCompilation.Trace.T_Trace_60 ->
  Maybe MAlonzo.Code.VerifiedCompilation.Trace.T_Trace_60
d_checkScope'7511'_100 v0
  = case coe v0 of
      MAlonzo.Code.VerifiedCompilation.Trace.C_step_64 v1 v2 v3 v4
        -> coe
             MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
             (coe d_checkScope_98 (coe v3))
             (coe
                (\ v5 ->
                   coe
                     MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                     (coe d_checkScope'7511'_100 (coe v4))
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
             (coe d_checkScope_98 (coe v1))
             (coe
                (\ v2 ->
                   coe
                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                     (coe MAlonzo.Code.VerifiedCompilation.Trace.C_done_66 (coe v2))))
      _ -> MAlonzo.RTE.mazUnreachableError
