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
  [MAlonzo.Code.Utils.T__'215'__426
     MAlonzo.Code.VerifiedCompilation.Trace.T_SimplifierTag_4
     (MAlonzo.Code.Utils.T__'215'__426
        MAlonzo.Code.VerifiedCompilation.Trace.T_Hints_52
        (MAlonzo.Code.Utils.T__'215'__426
           MAlonzo.Code.RawU.T_Untyped_208
           MAlonzo.Code.RawU.T_Untyped_208))] ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.VerifiedCompilation.T_Error_2
    MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_runCertifier_2 v0
  = coe
      MAlonzo.Code.Utils.du_eitherBind_54
      (coe
         MAlonzo.Code.Utils.du_try_94
         (coe MAlonzo.Code.VerifiedCompilation.Trace.d_toTrace_78 (coe v0))
         (coe MAlonzo.Code.VerifiedCompilation.C_emptyDump_4))
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Utils.du_eitherBind_54
              (coe
                 MAlonzo.Code.Utils.du_try_94
                 (coe
                    MAlonzo.Code.VerifiedCompilation.d_checkScope'7511'_100 (coe v1))
                 (coe MAlonzo.Code.VerifiedCompilation.C_illScoped_6))
              (coe
                 (\ v2 ->
                    coe
                      MAlonzo.Code.Utils.du_eitherBind_54
                      (coe MAlonzo.Code.VerifiedCompilation.d_certify_44 (coe v2))
                      (coe
                         (\ v3 ->
                            coe
                              MAlonzo.Code.Utils.C_inj'8322'_14
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                                 (coe v3))))))))
-- Certifier.runCertifierMain
runCertifierMain ::
  MAlonzo.Code.Agda.Builtin.List.T_List_10
    ()
    (MAlonzo.Code.Utils.T__'215'__426
       MAlonzo.Code.VerifiedCompilation.Trace.T_SimplifierTag_4
       (MAlonzo.Code.Utils.T__'215'__426
          MAlonzo.Code.VerifiedCompilation.Trace.T_Hints_52
          (MAlonzo.Code.Utils.T__'215'__426
             MAlonzo.Code.RawU.T_Untyped_208
             MAlonzo.Code.RawU.T_Untyped_208))) ->
  MAlonzo.Code.Agda.Builtin.Maybe.T_Maybe_10
    ()
    (MAlonzo.Code.Utils.T__'215'__426
       Bool MAlonzo.Code.Agda.Builtin.String.T_String_6)
runCertifierMain = coe d_runCertifierMain_12
d_runCertifierMain_12 ::
  [MAlonzo.Code.Utils.T__'215'__426
     MAlonzo.Code.VerifiedCompilation.Trace.T_SimplifierTag_4
     (MAlonzo.Code.Utils.T__'215'__426
        MAlonzo.Code.VerifiedCompilation.Trace.T_Hints_52
        (MAlonzo.Code.Utils.T__'215'__426
           MAlonzo.Code.RawU.T_Untyped_208
           MAlonzo.Code.RawU.T_Untyped_208))] ->
  Maybe
    (MAlonzo.Code.Utils.T__'215'__426
       Bool MAlonzo.Code.Agda.Builtin.String.T_String_6)
d_runCertifierMain_12 v0
  = let v1 = d_runCertifier_2 (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Utils.C_inj'8321'_12 v2
           -> case coe v2 of
                MAlonzo.Code.VerifiedCompilation.C_emptyDump_4
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                MAlonzo.Code.VerifiedCompilation.C_illScoped_6
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                MAlonzo.Code.VerifiedCompilation.C_counterExample_8 v3
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Utils.C__'44'__440
                          (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                          (coe MAlonzo.Code.CertifierReport.d_makeReport_264 (coe v1)))
                MAlonzo.Code.VerifiedCompilation.C_abort_10 v3
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Utils.C__'44'__440
                          (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                          (coe MAlonzo.Code.CertifierReport.d_makeReport_264 (coe v1)))
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Utils.C_inj'8322'_14 v2
           -> coe
                seq (coe v2)
                (coe
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                   (coe
                      MAlonzo.Code.Utils.C__'44'__440
                      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                      (coe MAlonzo.Code.CertifierReport.d_makeReport_264 (coe v1))))
         _ -> MAlonzo.RTE.mazUnreachableError)
