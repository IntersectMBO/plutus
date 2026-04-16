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
import qualified MAlonzo.Code.VerifiedCompilation.UForceCaseDelay
import qualified MAlonzo.Code.VerifiedCompilation.UForceDelay
import qualified MAlonzo.Code.VerifiedCompilation.UInline

-- VerifiedCompilation.Error
d_Error_2 = ()
data T_Error_2
  = C_emptyDump_4 | C_illScoped_6 |
    C_counterExample_8 (MAlonzo.Code.Utils.T_Either_6
                          MAlonzo.Code.VerifiedCompilation.Trace.T_UncertifiedOptTag_4
                          MAlonzo.Code.VerifiedCompilation.Trace.T_CertifiedOptTag_10) |
    C_abort_10 (MAlonzo.Code.Utils.T_Either_6
                  MAlonzo.Code.VerifiedCompilation.Trace.T_UncertifiedOptTag_4
                  MAlonzo.Code.VerifiedCompilation.Trace.T_CertifiedOptTag_10)
-- VerifiedCompilation.tagToRelation
d_tagToRelation_12 ::
  MAlonzo.Code.VerifiedCompilation.Trace.T_CertifiedOptTag_10 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> ()
d_tagToRelation_12 = erased
-- VerifiedCompilation.RelationOf
d_RelationOf_14 ::
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.VerifiedCompilation.Trace.T_UncertifiedOptTag_4
    MAlonzo.Code.VerifiedCompilation.Trace.T_CertifiedOptTag_10 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> ()
d_RelationOf_14 = erased
-- VerifiedCompilation.hasRelation
d_hasRelation_18 ::
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.VerifiedCompilation.Trace.T_UncertifiedOptTag_4
    MAlonzo.Code.VerifiedCompilation.Trace.T_CertifiedOptTag_10 ->
  Bool
d_hasRelation_18 = coe MAlonzo.Code.Utils.du_is'45'inj'8322'_46
-- VerifiedCompilation.certifyPass
d_certifyPass_26 ::
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.VerifiedCompilation.Trace.T_UncertifiedOptTag_4
    MAlonzo.Code.VerifiedCompilation.Trace.T_CertifiedOptTag_10 ->
  MAlonzo.Code.VerifiedCompilation.Trace.T_Hints_72 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_CertResult_12
d_certifyPass_26 v0 v1
  = case coe v0 of
      MAlonzo.Code.Utils.C_inj'8321'_12 v2
        -> coe
             (\ v3 v4 ->
                coe
                  MAlonzo.Code.VerifiedCompilation.NotImplemented.du_certNotImplemented_22)
      MAlonzo.Code.Utils.C_inj'8322'_14 v2
        -> case coe v2 of
             MAlonzo.Code.VerifiedCompilation.Trace.C_floatDelayT_12
               -> coe
                    MAlonzo.Code.VerifiedCompilation.Certificate.du_decider_192
                    (coe
                       MAlonzo.Code.VerifiedCompilation.UFloatDelay.d_isFloatDelay'63'_488
                       (coe (0 :: Integer)))
             MAlonzo.Code.VerifiedCompilation.Trace.C_forceDelayT_14
               -> coe
                    MAlonzo.Code.VerifiedCompilation.Certificate.du_decider_192
                    (coe
                       MAlonzo.Code.VerifiedCompilation.UForceDelay.d_isForceDelay'63'_178
                       (coe (0 :: Integer)))
             MAlonzo.Code.VerifiedCompilation.Trace.C_forceCaseDelayT_16
               -> coe
                    MAlonzo.Code.VerifiedCompilation.Certificate.du_decider_192
                    (coe
                       MAlonzo.Code.VerifiedCompilation.UForceCaseDelay.d_isForceCaseDelay'63'_94
                       (coe (0 :: Integer)))
             MAlonzo.Code.VerifiedCompilation.Trace.C_caseReduceT_18
               -> coe
                    MAlonzo.Code.VerifiedCompilation.Certificate.du_decider_192
                    (coe
                       MAlonzo.Code.VerifiedCompilation.UCaseReduce.d_isCaseReduce'63'_26
                       (coe (0 :: Integer)))
             MAlonzo.Code.VerifiedCompilation.Trace.C_inlineT_20
               -> case coe v1 of
                    MAlonzo.Code.VerifiedCompilation.Trace.C_inline_74 v3
                      -> coe
                           MAlonzo.Code.VerifiedCompilation.Certificate.du_checker_156
                           (coe
                              MAlonzo.Code.VerifiedCompilation.UInline.d_top'45'check_718
                              (coe v3))
                    MAlonzo.Code.VerifiedCompilation.Trace.C_none_76
                      -> coe
                           MAlonzo.Code.VerifiedCompilation.Certificate.C_abort_32
                           (coe MAlonzo.Code.VerifiedCompilation.Trace.d_InlineT_36)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.VerifiedCompilation.Trace.C_cseT_22
               -> coe
                    MAlonzo.Code.VerifiedCompilation.Certificate.du_decider_192
                    (coe
                       MAlonzo.Code.VerifiedCompilation.UCSE.d_isUntypedCSE'63'_26
                       (coe (0 :: Integer)))
             MAlonzo.Code.VerifiedCompilation.Trace.C_applyToCaseT_24
               -> coe
                    MAlonzo.Code.VerifiedCompilation.Certificate.du_decider_192
                    (coe
                       MAlonzo.Code.VerifiedCompilation.UApplyToCase.d_a2c'63''7580''7580'_24
                       (coe (0 :: Integer)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.Certificate
d_Certificate_34 ::
  MAlonzo.Code.VerifiedCompilation.Trace.T_Trace_80 -> ()
d_Certificate_34 = erased
-- VerifiedCompilation.certify
d_certify_46 ::
  MAlonzo.Code.VerifiedCompilation.Trace.T_Trace_80 ->
  MAlonzo.Code.Utils.T_Either_6 T_Error_2 AgdaAny
d_certify_46 v0
  = case coe v0 of
      MAlonzo.Code.VerifiedCompilation.Trace.C_step_84 v1 v2 v3 v4
        -> let v5
                 = coe
                     d_certifyPass_26 v1 v2 v3
                     (MAlonzo.Code.VerifiedCompilation.Trace.d_head_90 (coe v4)) in
           coe
             (case coe v5 of
                MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_18 v6
                  -> coe
                       MAlonzo.Code.Utils.du_eitherBind_54 (coe d_certify_46 (coe v4))
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
      MAlonzo.Code.VerifiedCompilation.Trace.C_done_86 v1
        -> coe
             MAlonzo.Code.Utils.C_inj'8322'_14
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.cert
d_cert_96 ::
  MAlonzo.Code.VerifiedCompilation.Trace.T_Trace_80 ->
  MAlonzo.Code.Utils.T_Either_6 T_Error_2 AgdaAny ->
  AgdaAny -> AgdaAny
d_cert_96 ~v0 v1 v2 = du_cert_96 v1 v2
du_cert_96 ::
  MAlonzo.Code.Utils.T_Either_6 T_Error_2 AgdaAny ->
  AgdaAny -> AgdaAny
du_cert_96 v0 v1
  = case coe v0 of
      MAlonzo.Code.Utils.C_inj'8322'_14 v2 -> coe seq (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.checkScope
d_checkScope_100 ::
  MAlonzo.Code.RawU.T_Untyped_208 ->
  Maybe MAlonzo.Code.Untyped.T__'8866'_14
d_checkScope_100 v0
  = coe
      MAlonzo.Code.Utils.du_eitherToMaybe_104
      (coe MAlonzo.Code.Untyped.d_scopeCheckU0_276 (coe v0))
-- VerifiedCompilation.checkScopeᵗ
d_checkScope'7511'_102 ::
  MAlonzo.Code.VerifiedCompilation.Trace.T_Trace_80 ->
  Maybe MAlonzo.Code.VerifiedCompilation.Trace.T_Trace_80
d_checkScope'7511'_102 v0
  = case coe v0 of
      MAlonzo.Code.VerifiedCompilation.Trace.C_step_84 v1 v2 v3 v4
        -> coe
             MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
             (coe d_checkScope_100 (coe v3))
             (coe
                (\ v5 ->
                   coe
                     MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                     (coe d_checkScope'7511'_102 (coe v4))
                     (coe
                        (\ v6 ->
                           coe
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                             (coe
                                MAlonzo.Code.VerifiedCompilation.Trace.C_step_84 (coe v1) (coe v2)
                                (coe v5) (coe v6))))))
      MAlonzo.Code.VerifiedCompilation.Trace.C_done_86 v1
        -> coe
             MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
             (coe d_checkScope_100 (coe v1))
             (coe
                (\ v2 ->
                   coe
                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                     (coe MAlonzo.Code.VerifiedCompilation.Trace.C_done_86 (coe v2))))
      _ -> MAlonzo.RTE.mazUnreachableError
