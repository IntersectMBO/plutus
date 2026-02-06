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
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.IO
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.RawU
import qualified MAlonzo.Code.Untyped
import qualified MAlonzo.Code.Utils
import qualified MAlonzo.Code.VerifiedCompilation.Certificate
import qualified MAlonzo.Code.VerifiedCompilation.NotImplemented
import qualified MAlonzo.Code.VerifiedCompilation.Trace
import qualified MAlonzo.Code.VerifiedCompilation.UCSE
import qualified MAlonzo.Code.VerifiedCompilation.UCaseOfCase
import qualified MAlonzo.Code.VerifiedCompilation.UCaseReduce
import qualified MAlonzo.Code.VerifiedCompilation.UFloatDelay
import qualified MAlonzo.Code.VerifiedCompilation.UForceDelay

import qualified Data.Text.IO as TextIO
import qualified System.IO as IO
import qualified Data.Text as Text
import PlutusCore.Compiler.Types
-- VerifiedCompilation.Error
d_Error_2 = ()
data T_Error_2
  = C_emptyDump_4 | C_illScoped_6 | C_counterExample_8 | C_abort_10
-- VerifiedCompilation.RelationOf
d_RelationOf_12 ::
  MAlonzo.Code.VerifiedCompilation.Trace.T_SimplifierTag_4 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> ()
d_RelationOf_12 = erased
-- VerifiedCompilation.certify
d_certify_16 ::
  MAlonzo.Code.VerifiedCompilation.Trace.T_SimplifierTag_4 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_CertResult_12
d_certify_16 v0
  = case coe v0 of
      MAlonzo.Code.VerifiedCompilation.Trace.C_floatDelayT_6
        -> coe
             MAlonzo.Code.VerifiedCompilation.UFloatDelay.d_certFloatDelay_702
      MAlonzo.Code.VerifiedCompilation.Trace.C_forceDelayT_8
        -> coe
             MAlonzo.Code.VerifiedCompilation.UForceDelay.d_certForceDelay_1738
      MAlonzo.Code.VerifiedCompilation.Trace.C_forceCaseDelayT_10
        -> coe
             (\ v1 v2 ->
                coe
                  MAlonzo.Code.VerifiedCompilation.NotImplemented.du_certNotImplemented_22)
      MAlonzo.Code.VerifiedCompilation.Trace.C_caseOfCaseT_12
        -> coe
             MAlonzo.Code.VerifiedCompilation.UCaseOfCase.d_certCaseOfCase_652
      MAlonzo.Code.VerifiedCompilation.Trace.C_caseReduceT_14
        -> coe
             MAlonzo.Code.VerifiedCompilation.UCaseReduce.d_certCaseReduce_152
      MAlonzo.Code.VerifiedCompilation.Trace.C_inlineT_16
        -> coe
             (\ v1 v2 ->
                coe
                  MAlonzo.Code.VerifiedCompilation.NotImplemented.du_certNotImplemented_22)
      MAlonzo.Code.VerifiedCompilation.Trace.C_cseT_18
        -> coe MAlonzo.Code.VerifiedCompilation.UCSE.d_certCSE_92
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.Certificate
d_Certificate_18 ::
  MAlonzo.Code.VerifiedCompilation.Trace.T_Trace_22 -> ()
d_Certificate_18 = erased
-- VerifiedCompilation.certifyᵗ
d_certify'7511'_30 ::
  MAlonzo.Code.VerifiedCompilation.Trace.T_Trace_22 ->
  MAlonzo.Code.Utils.T_Either_6 T_Error_2 AgdaAny
d_certify'7511'_30 v0
  = case coe v0 of
      MAlonzo.Code.VerifiedCompilation.Trace.C_step_26 v1 v2 v3
        -> let v4
                 = coe
                     d_certify_16 v1 v2
                     (MAlonzo.Code.VerifiedCompilation.Trace.d_head_32 (coe v3)) in
           coe
             (case coe v4 of
                MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_18 v5
                  -> coe
                       MAlonzo.Code.Utils.du_eitherBind_42
                       (coe d_certify'7511'_30 (coe v3))
                       (coe
                          (\ v6 ->
                             coe
                               MAlonzo.Code.Utils.C_inj'8322'_14
                               (coe MAlonzo.Code.Utils.C__'44'__428 (coe v5) (coe v6))))
                MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_26 v8 v9 v10
                  -> coe MAlonzo.Code.Utils.C_inj'8321'_12 (coe C_counterExample_8)
                MAlonzo.Code.VerifiedCompilation.Certificate.C_abort_32 v7 v8 v9
                  -> coe MAlonzo.Code.Utils.C_inj'8321'_12 (coe C_abort_10)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.VerifiedCompilation.Trace.C_done_28 v1
        -> coe
             MAlonzo.Code.Utils.C_inj'8322'_14
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.checkScope
d_checkScope_66 ::
  MAlonzo.Code.RawU.T_Untyped_208 ->
  Maybe MAlonzo.Code.Untyped.T__'8866'_14
d_checkScope_66 v0
  = coe
      MAlonzo.Code.Utils.du_eitherToMaybe_92
      (coe MAlonzo.Code.Untyped.d_scopeCheckU0_276 (coe v0))
-- VerifiedCompilation.checkScopeᵗ
d_checkScope'7511'_68 ::
  MAlonzo.Code.VerifiedCompilation.Trace.T_Trace_22 ->
  Maybe MAlonzo.Code.VerifiedCompilation.Trace.T_Trace_22
d_checkScope'7511'_68 v0
  = case coe v0 of
      MAlonzo.Code.VerifiedCompilation.Trace.C_step_26 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
             (coe d_checkScope_66 (coe v2))
             (coe
                (\ v4 ->
                   coe
                     MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                     (coe d_checkScope'7511'_68 (coe v3))
                     (coe
                        (\ v5 ->
                           coe
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                             (coe
                                MAlonzo.Code.VerifiedCompilation.Trace.C_step_26 (coe v1) (coe v4)
                                (coe v5))))))
      MAlonzo.Code.VerifiedCompilation.Trace.C_done_28 v1
        -> coe
             MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
             (coe d_checkScope_66 (coe v1))
             (coe
                (\ v2 ->
                   coe
                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                     (coe MAlonzo.Code.VerifiedCompilation.Trace.C_done_28 (coe v2))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.runCertifier
d_runCertifier_86 ::
  MAlonzo.Code.Utils.T_List_432
    (MAlonzo.Code.Utils.T__'215'__414
       MAlonzo.Code.VerifiedCompilation.Trace.T_SimplifierTag_4
       (MAlonzo.Code.Utils.T__'215'__414
          MAlonzo.Code.RawU.T_Untyped_208
          MAlonzo.Code.RawU.T_Untyped_208)) ->
  MAlonzo.Code.Utils.T_Either_6
    T_Error_2 MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_runCertifier_86 v0
  = coe
      MAlonzo.Code.Utils.du_eitherBind_42
      (coe
         MAlonzo.Code.Utils.du_try_82
         (coe MAlonzo.Code.VerifiedCompilation.Trace.d_toTrace_40 (coe v0))
         (coe C_emptyDump_4))
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Utils.du_eitherBind_42
              (coe
                 MAlonzo.Code.Utils.du_try_82 (coe d_checkScope'7511'_68 (coe v1))
                 (coe C_illScoped_6))
              (coe
                 (\ v2 ->
                    coe
                      MAlonzo.Code.Utils.du_eitherBind_42
                      (coe d_certify'7511'_30 (coe v2))
                      (coe
                         (\ v3 ->
                            coe
                              MAlonzo.Code.Utils.C_inj'8322'_14
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                                 (coe v3))))))))
-- VerifiedCompilation.passed?
d_passed'63'_100 ::
  () -> () -> MAlonzo.Code.Utils.T_Either_6 AgdaAny AgdaAny -> Bool
d_passed'63'_100 ~v0 ~v1 v2 = du_passed'63'_100 v2
du_passed'63'_100 ::
  MAlonzo.Code.Utils.T_Either_6 AgdaAny AgdaAny -> Bool
du_passed'63'_100 v0
  = case coe v0 of
      MAlonzo.Code.Utils.C_inj'8321'_12 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Utils.C_inj'8322'_14 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.FileHandle
type T_FileHandle_102 = IO.Handle
d_FileHandle_102
  = error
      "MAlonzo Runtime Error: postulate evaluated: VerifiedCompilation.FileHandle"
-- VerifiedCompilation.writeFile
d_writeFile_104 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.IO.T_IO_8
    () MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_writeFile_104 = \f -> TextIO.writeFile (Text.unpack f)
-- VerifiedCompilation.stderr
d_stderr_106 :: T_FileHandle_102
d_stderr_106 = IO.stderr
-- VerifiedCompilation.hPutStrLn
d_hPutStrLn_108 ::
  T_FileHandle_102 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.IO.T_IO_8
    () MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_hPutStrLn_108 = TextIO.hPutStr
-- VerifiedCompilation.putStrLn
d_putStrLn_110 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.IO.T_IO_8
    () MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_putStrLn_110 = TextIO.putStrLn
-- VerifiedCompilation.runCertifierMain
runCertifierMain ::
  MAlonzo.Code.Utils.T_List_432
    (MAlonzo.Code.Utils.T__'215'__414
       MAlonzo.Code.VerifiedCompilation.Trace.T_SimplifierTag_4
       (MAlonzo.Code.Utils.T__'215'__414
          MAlonzo.Code.RawU.T_Untyped_208
          MAlonzo.Code.RawU.T_Untyped_208)) ->
  MAlonzo.Code.Agda.Builtin.Maybe.T_Maybe_10 () Bool
runCertifierMain = coe d_runCertifierMain_112
d_runCertifierMain_112 ::
  MAlonzo.Code.Utils.T_List_432
    (MAlonzo.Code.Utils.T__'215'__414
       MAlonzo.Code.VerifiedCompilation.Trace.T_SimplifierTag_4
       (MAlonzo.Code.Utils.T__'215'__414
          MAlonzo.Code.RawU.T_Untyped_208
          MAlonzo.Code.RawU.T_Untyped_208)) ->
  Maybe Bool
d_runCertifierMain_112 v0
  = let v1
          = coe
              MAlonzo.Code.Utils.du_eitherBind_42
              (coe
                 MAlonzo.Code.Data.Maybe.Base.du_maybe_32
                 (coe MAlonzo.Code.Utils.C_inj'8322'_14)
                 (coe MAlonzo.Code.Utils.C_inj'8321'_12 (coe C_emptyDump_4))
                 (coe MAlonzo.Code.VerifiedCompilation.Trace.d_toTrace_40 (coe v0)))
              (coe
                 (\ v1 ->
                    coe
                      MAlonzo.Code.Utils.du_eitherBind_42
                      (coe
                         MAlonzo.Code.Utils.du_try_82 (coe d_checkScope'7511'_68 (coe v1))
                         (coe C_illScoped_6))
                      (coe
                         (\ v2 ->
                            coe
                              MAlonzo.Code.Utils.du_eitherBind_42
                              (coe d_certify'7511'_30 (coe v2))
                              (coe
                                 (\ v3 ->
                                    coe
                                      MAlonzo.Code.Utils.C_inj'8322'_14
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                                         (coe v3)))))))) in
    coe
      (case coe v1 of
         MAlonzo.Code.Utils.C_inj'8321'_12 v2
           -> case coe v2 of
                C_emptyDump_4 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                C_illScoped_6 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                C_counterExample_8
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                C_abort_10
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Utils.C_inj'8322'_14 v2
           -> coe
                seq (coe v2)
                (coe
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
         _ -> MAlonzo.RTE.mazUnreachableError)
