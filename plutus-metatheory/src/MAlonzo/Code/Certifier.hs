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

module MAlonzo.Code.Certifier where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.CertifierReport
import qualified MAlonzo.Code.RawU
import qualified MAlonzo.Code.Utils
import qualified MAlonzo.Code.VerifiedCompilation
import qualified MAlonzo.Code.VerifiedCompilation.Trace

-- Certifier.runCertifier
d_runCertifier_2 ::
  MAlonzo.Code.VerifiedCompilation.Trace.T_NonEmptySep_90
    (MAlonzo.Code.Utils.T__'215'__436
       (MAlonzo.Code.Utils.T_Either_6
          MAlonzo.Code.VerifiedCompilation.Trace.T_UncertifiedOptTag_4
          MAlonzo.Code.VerifiedCompilation.Trace.T_CertifiedOptTag_10)
       MAlonzo.Code.VerifiedCompilation.Trace.T_Hints_80)
    MAlonzo.Code.RawU.T_Untyped_210 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.VerifiedCompilation.T_Error_2
    MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_runCertifier_2 v0
  = coe
      MAlonzo.Code.Utils.du_eitherBind_54
      (coe
         MAlonzo.Code.Utils.du_try_102
         (coe
            MAlonzo.Code.VerifiedCompilation.d_checkScope'7511'_102 (coe v0))
         (coe MAlonzo.Code.VerifiedCompilation.C_illScoped_6))
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Utils.du_eitherBind_54
              (coe MAlonzo.Code.VerifiedCompilation.d_certify_46 (coe v1))
              (coe
                 (\ v2 ->
                    coe
                      MAlonzo.Code.Utils.C_inj'8322'_14
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))))))
-- Certifier.runCertifierMain
runCertifierMain ::
  MAlonzo.Code.VerifiedCompilation.Trace.T_NonEmptySep_90
    (MAlonzo.Code.Utils.T__'215'__436
       (MAlonzo.Code.Utils.T_Either_6
          MAlonzo.Code.VerifiedCompilation.Trace.T_UncertifiedOptTag_4
          MAlonzo.Code.VerifiedCompilation.Trace.T_CertifiedOptTag_10)
       MAlonzo.Code.VerifiedCompilation.Trace.T_Hints_80)
    MAlonzo.Code.RawU.T_Untyped_210 ->
  MAlonzo.Code.Agda.Builtin.List.T_List_10
    () MAlonzo.Code.VerifiedCompilation.Trace.T_EvalResult_122 ->
  MAlonzo.Code.Agda.Builtin.Maybe.T_Maybe_10
    ()
    (MAlonzo.Code.Utils.T__'215'__436
       Bool MAlonzo.Code.Agda.Builtin.String.T_String_6)
runCertifierMain = coe d_runCertifierMain_10
d_runCertifierMain_10 ::
  MAlonzo.Code.VerifiedCompilation.Trace.T_NonEmptySep_90
    (MAlonzo.Code.Utils.T__'215'__436
       (MAlonzo.Code.Utils.T_Either_6
          MAlonzo.Code.VerifiedCompilation.Trace.T_UncertifiedOptTag_4
          MAlonzo.Code.VerifiedCompilation.Trace.T_CertifiedOptTag_10)
       MAlonzo.Code.VerifiedCompilation.Trace.T_Hints_80)
    MAlonzo.Code.RawU.T_Untyped_210 ->
  [MAlonzo.Code.VerifiedCompilation.Trace.T_EvalResult_122] ->
  Maybe
    (MAlonzo.Code.Utils.T__'215'__436
       Bool MAlonzo.Code.Agda.Builtin.String.T_String_6)
d_runCertifierMain_10 v0 v1
  = let v2 = d_runCertifier_2 (coe v0) in
    coe
      (case coe v2 of
         MAlonzo.Code.Utils.C_inj'8321'_12 v3
           -> case coe v3 of
                MAlonzo.Code.VerifiedCompilation.C_emptyDump_4
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                MAlonzo.Code.VerifiedCompilation.C_illScoped_6
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                MAlonzo.Code.VerifiedCompilation.C_counterExample_8 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Utils.C__'44'__450
                          (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                          (coe
                             MAlonzo.Code.CertifierReport.d_makeReport_292 (coe v2) (coe v1)))
                MAlonzo.Code.VerifiedCompilation.C_abort_10 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Utils.C__'44'__450
                          (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                          (coe
                             MAlonzo.Code.CertifierReport.d_makeReport_292 (coe v2) (coe v1)))
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Utils.C_inj'8322'_14 v3
           -> coe
                seq (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                   (coe
                      MAlonzo.Code.Utils.C__'44'__450
                      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                      (coe
                         MAlonzo.Code.CertifierReport.d_makeReport_292 (coe v2) (coe v1))))
         _ -> MAlonzo.RTE.mazUnreachableError)
