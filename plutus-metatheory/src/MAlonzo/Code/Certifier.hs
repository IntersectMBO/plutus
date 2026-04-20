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
  [MAlonzo.Code.Utils.T__'215'__428
     (MAlonzo.Code.Utils.T_Either_6
        MAlonzo.Code.VerifiedCompilation.Trace.T_UncertifiedOptTag_4
        MAlonzo.Code.VerifiedCompilation.Trace.T_CertifiedOptTag_12)
     (MAlonzo.Code.Utils.T__'215'__428
        MAlonzo.Code.VerifiedCompilation.Trace.T_Hints_72
        (MAlonzo.Code.Utils.T__'215'__428
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
         (coe MAlonzo.Code.VerifiedCompilation.Trace.d_toTrace_98 (coe v0))
         (coe MAlonzo.Code.VerifiedCompilation.C_emptyDump_4))
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Utils.du_eitherBind_54
              (coe
                 MAlonzo.Code.Utils.du_try_94
                 (coe
                    MAlonzo.Code.VerifiedCompilation.d_checkScope'7511'_102 (coe v1))
                 (coe MAlonzo.Code.VerifiedCompilation.C_illScoped_6))
              (coe
                 (\ v2 ->
                    coe
                      MAlonzo.Code.Utils.du_eitherBind_54
                      (coe MAlonzo.Code.VerifiedCompilation.d_certify_46 (coe v2))
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
    (MAlonzo.Code.Utils.T__'215'__428
       (MAlonzo.Code.Utils.T_Either_6
          MAlonzo.Code.VerifiedCompilation.Trace.T_UncertifiedOptTag_4
          MAlonzo.Code.VerifiedCompilation.Trace.T_CertifiedOptTag_12)
       (MAlonzo.Code.Utils.T__'215'__428
          MAlonzo.Code.VerifiedCompilation.Trace.T_Hints_72
          (MAlonzo.Code.Utils.T__'215'__428
             MAlonzo.Code.RawU.T_Untyped_208
             MAlonzo.Code.RawU.T_Untyped_208))) ->
  MAlonzo.Code.Agda.Builtin.List.T_List_10
    () MAlonzo.Code.VerifiedCompilation.Trace.T_EvalResult_134 ->
  MAlonzo.Code.Agda.Builtin.Maybe.T_Maybe_10
    ()
    (MAlonzo.Code.Utils.T__'215'__428
       Bool MAlonzo.Code.Agda.Builtin.String.T_String_6)
runCertifierMain = coe d_runCertifierMain_12
d_runCertifierMain_12 ::
  [MAlonzo.Code.Utils.T__'215'__428
     (MAlonzo.Code.Utils.T_Either_6
        MAlonzo.Code.VerifiedCompilation.Trace.T_UncertifiedOptTag_4
        MAlonzo.Code.VerifiedCompilation.Trace.T_CertifiedOptTag_12)
     (MAlonzo.Code.Utils.T__'215'__428
        MAlonzo.Code.VerifiedCompilation.Trace.T_Hints_72
        (MAlonzo.Code.Utils.T__'215'__428
           MAlonzo.Code.RawU.T_Untyped_208
           MAlonzo.Code.RawU.T_Untyped_208))] ->
  [MAlonzo.Code.VerifiedCompilation.Trace.T_EvalResult_134] ->
  Maybe
    (MAlonzo.Code.Utils.T__'215'__428
       Bool MAlonzo.Code.Agda.Builtin.String.T_String_6)
d_runCertifierMain_12 v0 v1
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
                          MAlonzo.Code.Utils.C__'44'__442
                          (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                          (coe
                             MAlonzo.Code.CertifierReport.d_makeReport_284 (coe v2) (coe v1)))
                MAlonzo.Code.VerifiedCompilation.C_abort_10 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Utils.C__'44'__442
                          (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                          (coe
                             MAlonzo.Code.CertifierReport.d_makeReport_284 (coe v2) (coe v1)))
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Utils.C_inj'8322'_14 v3
           -> coe
                seq (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                   (coe
                      MAlonzo.Code.Utils.C__'44'__442
                      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                      (coe
                         MAlonzo.Code.CertifierReport.d_makeReport_284 (coe v2) (coe v1))))
         _ -> MAlonzo.RTE.mazUnreachableError)
