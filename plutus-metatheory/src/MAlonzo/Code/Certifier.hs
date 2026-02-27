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
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.CertifierReport
import qualified MAlonzo.Code.RawU
import qualified MAlonzo.Code.Untyped
import qualified MAlonzo.Code.Utils
import qualified MAlonzo.Code.VerifiedCompilation
import qualified MAlonzo.Code.VerifiedCompilation.Certificate

-- Certifier.runCertifier
d_runCertifier_2 ::
  MAlonzo.Code.Utils.T_List_414
    (MAlonzo.Code.Utils.T__'215'__396
       MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4
       (MAlonzo.Code.Utils.T__'215'__396
          MAlonzo.Code.VerifiedCompilation.Certificate.T_Hints_46
          (MAlonzo.Code.Utils.T__'215'__396
             MAlonzo.Code.RawU.T_Untyped_208
             MAlonzo.Code.RawU.T_Untyped_208))) ->
  Maybe MAlonzo.Code.VerifiedCompilation.T_Cert_656
d_runCertifier_2 v0
  = let v1
          = coe
              MAlonzo.Code.VerifiedCompilation.du_traverseEitherList_534
              (coe MAlonzo.Code.Untyped.d_scopeCheckU0_276) (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Utils.C_inj'8321'_12 v2
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
         MAlonzo.Code.Utils.C_inj'8322'_14 v2
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   MAlonzo.Code.VerifiedCompilation.C_cert_662 (coe (0 :: Integer))
                   (coe v2)
                   (coe
                      MAlonzo.Code.VerifiedCompilation.d_isTrace'63'_362
                      (coe (0 :: Integer)) (coe v2)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Certifier.runCertifierMain
runCertifierMain ::
  MAlonzo.Code.Utils.T_List_414
    (MAlonzo.Code.Utils.T__'215'__396
       MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4
       (MAlonzo.Code.Utils.T__'215'__396
          MAlonzo.Code.VerifiedCompilation.Certificate.T_Hints_46
          (MAlonzo.Code.Utils.T__'215'__396
             MAlonzo.Code.RawU.T_Untyped_208
             MAlonzo.Code.RawU.T_Untyped_208))) ->
  MAlonzo.Code.Agda.Builtin.Maybe.T_Maybe_10
    ()
    (MAlonzo.Code.Utils.T__'215'__396
       Bool MAlonzo.Code.Agda.Builtin.String.T_String_6)
runCertifierMain = coe d_runCertifierMain_16
d_runCertifierMain_16 ::
  MAlonzo.Code.Utils.T_List_414
    (MAlonzo.Code.Utils.T__'215'__396
       MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4
       (MAlonzo.Code.Utils.T__'215'__396
          MAlonzo.Code.VerifiedCompilation.Certificate.T_Hints_46
          (MAlonzo.Code.Utils.T__'215'__396
             MAlonzo.Code.RawU.T_Untyped_208
             MAlonzo.Code.RawU.T_Untyped_208))) ->
  Maybe
    (MAlonzo.Code.Utils.T__'215'__396
       Bool MAlonzo.Code.Agda.Builtin.String.T_String_6)
d_runCertifierMain_16 v0
  = let v1
          = coe
              MAlonzo.Code.VerifiedCompilation.du_traverseEitherList_534
              (coe MAlonzo.Code.Untyped.d_scopeCheckU0_276) (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Utils.C_inj'8321'_12 v2
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
         MAlonzo.Code.Utils.C_inj'8322'_14 v2
           -> let v3 = 0 :: Integer in
              coe
                (let v4
                       = MAlonzo.Code.VerifiedCompilation.d_isTrace'63'_362
                           (coe (0 :: Integer)) (coe v2) in
                 coe
                   (case coe v4 of
                      MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_66 v5
                        -> coe
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                             (coe
                                MAlonzo.Code.Utils.C__'44'__410
                                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                                (coe
                                   MAlonzo.Code.CertifierReport.d_makeReport_210 (coe v3) (coe v2)
                                   (coe v4)))
                      MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_74 v8 v9 v10
                        -> coe
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                             (coe
                                MAlonzo.Code.Utils.C__'44'__410
                                (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                (coe
                                   MAlonzo.Code.CertifierReport.d_makeReport_210 (coe v3) (coe v2)
                                   (coe
                                      MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_74 v8 v9
                                      v10)))
                      MAlonzo.Code.VerifiedCompilation.Certificate.C_abort_80 v7 v8 v9
                        -> coe
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                             (coe
                                MAlonzo.Code.Utils.C__'44'__410
                                (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                (coe
                                   MAlonzo.Code.CertifierReport.d_makeReport_210 (coe v3) (coe v2)
                                   (coe
                                      MAlonzo.Code.VerifiedCompilation.Certificate.C_abort_80 v7 v8
                                      v9)))
                      _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
