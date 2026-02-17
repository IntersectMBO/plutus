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

module MAlonzo.Code.VerifiedCompilation.UForceCaseDelay where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects
import qualified MAlonzo.Code.Untyped
import qualified MAlonzo.Code.VerifiedCompilation.Certificate
import qualified MAlonzo.Code.VerifiedCompilation.Trace
import qualified MAlonzo.Code.VerifiedCompilation.UntypedTranslation
import qualified MAlonzo.Code.VerifiedCompilation.UntypedViews

-- VerifiedCompilation.UForceCaseDelay.IsBranch
d_IsBranch_18 a0 a1 = ()
data T_IsBranch_18 = C_B'45'delay_20 | C_B'45'ƛ_22 T_IsBranch_18
-- VerifiedCompilation.UForceCaseDelay.isBranch?
d_isBranch'63'_26 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_isBranch'63'_26 ~v0 v1 = du_isBranch'63'_26 v1
du_isBranch'63'_26 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_isBranch'63'_26 v0
  = case coe v0 of
      MAlonzo.Code.Untyped.C_'96'_18 v1
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      MAlonzo.Code.Untyped.C_ƛ_20 v1
        -> let v2 = coe du_isBranch'63'_26 (coe v1) in
           coe
             (case coe v2 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
                  -> if coe v3
                       then case coe v4 of
                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v5
                                -> coe
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                     (coe v3)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                        (coe C_B'45'ƛ_22 v5))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       else coe
                              seq (coe v4)
                              (coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                 (coe v3)
                                 (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Untyped.C__'183'__22 v1 v2
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      MAlonzo.Code.Untyped.C_force_24 v1
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      MAlonzo.Code.Untyped.C_delay_26 v1
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                (coe C_B'45'delay_20))
      MAlonzo.Code.Untyped.C_con_28 v1
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      MAlonzo.Code.Untyped.C_constr_34 v1 v2
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      MAlonzo.Code.Untyped.C_case_40 v1 v2
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      MAlonzo.Code.Untyped.C_builtin_44 v1
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      MAlonzo.Code.Untyped.C_error_46
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.UForceCaseDelay.removeDelay
d_removeDelay_68 ::
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14]
d_removeDelay_68 ~v0 v1 = du_removeDelay_68 v1
du_removeDelay_68 ::
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14]
du_removeDelay_68 v0
  = coe MAlonzo.Code.Data.List.Base.du_map_22 (coe du_go_76) (coe v0)
-- VerifiedCompilation.UForceCaseDelay._.go
d_go_76 ::
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14
d_go_76 ~v0 ~v1 ~v2 v3 = du_go_76 v3
du_go_76 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14
du_go_76 v0
  = case coe v0 of
      MAlonzo.Code.Untyped.C_ƛ_20 v1
        -> coe MAlonzo.Code.Untyped.C_ƛ_20 (coe du_go_76 (coe v1))
      MAlonzo.Code.Untyped.C_delay_26 v1 -> coe v1
      _ -> coe v0
-- VerifiedCompilation.UForceCaseDelay.FCD
d_FCD_84 a0 a1 a2 = ()
data T_FCD_84
  = C_isFCD_86 MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
               MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_12
               MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
-- VerifiedCompilation.UForceCaseDelay.ForceCaseDelay
d_ForceCaseDelay_92 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> ()
d_ForceCaseDelay_92 = erased
-- VerifiedCompilation.UForceCaseDelay.isForceCaseDelay?
d_isForceCaseDelay'63'_94 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_38
d_isForceCaseDelay'63'_94 v0
  = coe
      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.du_translation'63'_164
      (coe v0)
      (coe MAlonzo.Code.VerifiedCompilation.Trace.C_forceCaseDelayT_10)
      (coe d_isFCD'63'_96)
-- VerifiedCompilation.UForceCaseDelay.isFCD?
d_isFCD'63'_96 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_38
d_isFCD'63'_96 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isForce'63'_286
              (coe v0)
              (coe
                 (\ v3 ->
                    coe
                      MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isCase'63'_600
                      (coe v3)
                      (\ v4 v5 ->
                         coe
                           MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_784)
                      (\ v4 v5 ->
                         coe
                           MAlonzo.Code.VerifiedCompilation.UntypedViews.du_allTerms'63'_800)))
              (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then case coe v5 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v6
                         -> case coe v6 of
                              MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isforce_278 v8
                                -> case coe v1 of
                                     MAlonzo.Code.Untyped.C_force_24 v9
                                       -> case coe v8 of
                                            MAlonzo.Code.VerifiedCompilation.UntypedViews.C_iscase_588 v12 v13
                                              -> case coe v9 of
                                                   MAlonzo.Code.Untyped.C_case_40 v14 v15
                                                     -> coe
                                                          seq (coe v12)
                                                          (coe
                                                             seq (coe v13)
                                                             (let v16
                                                                    = coe
                                                                        MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isCase'63'_600
                                                                        (coe v0)
                                                                        (\ v16 v17 ->
                                                                           coe
                                                                             MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_784)
                                                                        (\ v16 v17 ->
                                                                           coe
                                                                             MAlonzo.Code.VerifiedCompilation.UntypedViews.du_allTerms'63'_800)
                                                                        (coe v2) in
                                                              coe
                                                                (case coe v16 of
                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                     -> if coe v17
                                                                          then case coe v18 of
                                                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v19
                                                                                   -> case coe
                                                                                             v19 of
                                                                                        MAlonzo.Code.VerifiedCompilation.UntypedViews.C_iscase_588 v22 v23
                                                                                          -> case coe
                                                                                                    v2 of
                                                                                               MAlonzo.Code.Untyped.C_case_40 v24 v25
                                                                                                 -> coe
                                                                                                      seq
                                                                                                      (coe
                                                                                                         v22)
                                                                                                      (coe
                                                                                                         seq
                                                                                                         (coe
                                                                                                            v23)
                                                                                                         (let v26
                                                                                                                = coe
                                                                                                                    MAlonzo.Code.Data.List.Relation.Unary.All.du_all'63'_506
                                                                                                                    (coe
                                                                                                                       du_isBranch'63'_26)
                                                                                                                    (coe
                                                                                                                       v15) in
                                                                                                          coe
                                                                                                            (case coe
                                                                                                                    v26 of
                                                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v27 v28
                                                                                                                 -> if coe
                                                                                                                         v27
                                                                                                                      then case coe
                                                                                                                                  v28 of
                                                                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v29
                                                                                                                               -> let v30
                                                                                                                                        = coe
                                                                                                                                            d_isForceCaseDelay'63'_94
                                                                                                                                            v0
                                                                                                                                            v14
                                                                                                                                            v24 in
                                                                                                                                  coe
                                                                                                                                    (case coe
                                                                                                                                            v30 of
                                                                                                                                       MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_44 v31
                                                                                                                                         -> let v32
                                                                                                                                                  = coe
                                                                                                                                                      MAlonzo.Code.VerifiedCompilation.Certificate.du_pcePointwise_304
                                                                                                                                                      (coe
                                                                                                                                                         MAlonzo.Code.VerifiedCompilation.Trace.C_forceCaseDelayT_10)
                                                                                                                                                      (coe
                                                                                                                                                         d_isForceCaseDelay'63'_94
                                                                                                                                                         (coe
                                                                                                                                                            v0))
                                                                                                                                                      (coe
                                                                                                                                                         MAlonzo.Code.Data.List.Base.du_map_22
                                                                                                                                                         (coe
                                                                                                                                                            du_go_76)
                                                                                                                                                         (coe
                                                                                                                                                            v15))
                                                                                                                                                      (coe
                                                                                                                                                         v25) in
                                                                                                                                            coe
                                                                                                                                              (case coe
                                                                                                                                                      v32 of
                                                                                                                                                 MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_44 v33
                                                                                                                                                   -> coe
                                                                                                                                                        MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_44
                                                                                                                                                        (coe
                                                                                                                                                           C_isFCD_86
                                                                                                                                                           v29
                                                                                                                                                           v31
                                                                                                                                                           v33)
                                                                                                                                                 MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52 v36 v37 v38
                                                                                                                                                   -> coe
                                                                                                                                                        MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52
                                                                                                                                                        (coe
                                                                                                                                                           MAlonzo.Code.VerifiedCompilation.Trace.C_forceCaseDelayT_10)
                                                                                                                                                        v1
                                                                                                                                                        v2
                                                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                       MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52 v34 v35 v36
                                                                                                                                         -> coe
                                                                                                                                              MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52
                                                                                                                                              (coe
                                                                                                                                                 MAlonzo.Code.VerifiedCompilation.Trace.C_forceCaseDelayT_10)
                                                                                                                                              v1
                                                                                                                                              v2
                                                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                      else coe
                                                                                                                             seq
                                                                                                                             (coe
                                                                                                                                v28)
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52
                                                                                                                                (coe
                                                                                                                                   MAlonzo.Code.VerifiedCompilation.Trace.C_forceCaseDelayT_10)
                                                                                                                                v1
                                                                                                                                v2)
                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError)))
                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                          else coe
                                                                                 seq (coe v18)
                                                                                 (coe
                                                                                    MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52
                                                                                    (coe
                                                                                       MAlonzo.Code.VerifiedCompilation.Trace.C_forceCaseDelayT_10)
                                                                                    v1 v2)
                                                                   _ -> MAlonzo.RTE.mazUnreachableError)))
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v5)
                       (coe
                          MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52
                          (coe MAlonzo.Code.VerifiedCompilation.Trace.C_forceCaseDelayT_10)
                          v1 v2)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.UForceCaseDelay..extendedlambda1
d_'46'extendedlambda1_112 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isForce_270 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  T_FCD_84 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda1_112 = erased
-- VerifiedCompilation.UForceCaseDelay..extendedlambda2
d_'46'extendedlambda2_142 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isCase_576 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  T_FCD_84 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda2_142 = erased
-- VerifiedCompilation.UForceCaseDelay..extendedlambda3
d_'46'extendedlambda3_180 ::
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  (MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  T_FCD_84 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda3_180 = erased
-- VerifiedCompilation.UForceCaseDelay..extendedlambda4
d_'46'extendedlambda4_228 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Trace.T_SimplifierTag_4 ->
  AgdaAny ->
  AgdaAny ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  T_FCD_84 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda4_228 = erased
-- VerifiedCompilation.UForceCaseDelay..extendedlambda5
d_'46'extendedlambda5_280 ::
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  (MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Trace.T_SimplifierTag_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_FCD_84 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda5_280 = erased
-- VerifiedCompilation.UForceCaseDelay.fstTest1
d_fstTest1_306 :: Integer -> MAlonzo.Code.Untyped.T__'8866'_14
d_fstTest1_306 ~v0 = du_fstTest1_306
du_fstTest1_306 :: MAlonzo.Code.Untyped.T__'8866'_14
du_fstTest1_306
  = coe
      MAlonzo.Code.Untyped.C_force_24
      (coe
         MAlonzo.Code.Untyped.C_case_40
         (coe MAlonzo.Code.Untyped.C_error_46)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Untyped.C_delay_26
               (coe MAlonzo.Code.Untyped.C_error_46))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
-- VerifiedCompilation.UForceCaseDelay.sndTest1
d_sndTest1_308 :: Integer -> MAlonzo.Code.Untyped.T__'8866'_14
d_sndTest1_308 ~v0 = du_sndTest1_308
du_sndTest1_308 :: MAlonzo.Code.Untyped.T__'8866'_14
du_sndTest1_308
  = coe
      MAlonzo.Code.Untyped.C_case_40
      (coe MAlonzo.Code.Untyped.C_error_46)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe MAlonzo.Code.Untyped.C_error_46)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- VerifiedCompilation.UForceCaseDelay.test1
d_test1_310 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_test1_310 = erased
-- VerifiedCompilation.UForceCaseDelay.fstTest2
d_fstTest2_312 :: Integer -> MAlonzo.Code.Untyped.T__'8866'_14
d_fstTest2_312 ~v0 = du_fstTest2_312
du_fstTest2_312 :: MAlonzo.Code.Untyped.T__'8866'_14
du_fstTest2_312
  = coe
      MAlonzo.Code.Untyped.C_force_24
      (coe
         MAlonzo.Code.Untyped.C_case_40
         (coe MAlonzo.Code.Untyped.C_error_46)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Untyped.C_delay_26
               (coe MAlonzo.Code.Untyped.C_error_46))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
-- VerifiedCompilation.UForceCaseDelay.sndTest2
d_sndTest2_314 :: Integer -> MAlonzo.Code.Untyped.T__'8866'_14
d_sndTest2_314 ~v0 = du_sndTest2_314
du_sndTest2_314 :: MAlonzo.Code.Untyped.T__'8866'_14
du_sndTest2_314
  = coe
      MAlonzo.Code.Untyped.C_case_40
      (coe MAlonzo.Code.Untyped.C_error_46)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Untyped.C_delay_26
            (coe MAlonzo.Code.Untyped.C_error_46))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- VerifiedCompilation.UForceCaseDelay.test2
d_test2_316 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_test2_316 = erased
-- VerifiedCompilation.UForceCaseDelay.fstTest3
d_fstTest3_318 :: Integer -> MAlonzo.Code.Untyped.T__'8866'_14
d_fstTest3_318 ~v0 = du_fstTest3_318
du_fstTest3_318 :: MAlonzo.Code.Untyped.T__'8866'_14
du_fstTest3_318
  = coe
      MAlonzo.Code.Untyped.C_case_40
      (coe MAlonzo.Code.Untyped.C_error_46)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Untyped.C_ƛ_20
            (coe
               MAlonzo.Code.Untyped.C_force_24
               (coe
                  MAlonzo.Code.Untyped.C_case_40
                  (coe MAlonzo.Code.Untyped.C_error_46)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Untyped.C_delay_26
                        (coe MAlonzo.Code.Untyped.C_error_46))
                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- VerifiedCompilation.UForceCaseDelay.sndTest3
d_sndTest3_320 :: Integer -> MAlonzo.Code.Untyped.T__'8866'_14
d_sndTest3_320 ~v0 = du_sndTest3_320
du_sndTest3_320 :: MAlonzo.Code.Untyped.T__'8866'_14
du_sndTest3_320
  = coe
      MAlonzo.Code.Untyped.C_case_40
      (coe MAlonzo.Code.Untyped.C_error_46)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Untyped.C_ƛ_20
            (coe
               MAlonzo.Code.Untyped.C_case_40
               (coe MAlonzo.Code.Untyped.C_error_46)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe MAlonzo.Code.Untyped.C_error_46)
                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- VerifiedCompilation.UForceCaseDelay.test3
d_test3_322 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_test3_322 = erased
-- VerifiedCompilation.UForceCaseDelay.fstTest4
d_fstTest4_324 :: Integer -> MAlonzo.Code.Untyped.T__'8866'_14
d_fstTest4_324 ~v0 = du_fstTest4_324
du_fstTest4_324 :: MAlonzo.Code.Untyped.T__'8866'_14
du_fstTest4_324
  = coe
      MAlonzo.Code.Untyped.C_case_40
      (coe MAlonzo.Code.Untyped.C_error_46)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Untyped.C_ƛ_20
            (coe
               MAlonzo.Code.Untyped.C_force_24
               (coe
                  MAlonzo.Code.Untyped.C_case_40
                  (coe MAlonzo.Code.Untyped.C_error_46)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Untyped.C_delay_26
                        (coe MAlonzo.Code.Untyped.C_error_46))
                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- VerifiedCompilation.UForceCaseDelay.sndTest4
d_sndTest4_326 :: Integer -> MAlonzo.Code.Untyped.T__'8866'_14
d_sndTest4_326 ~v0 = du_sndTest4_326
du_sndTest4_326 :: MAlonzo.Code.Untyped.T__'8866'_14
du_sndTest4_326
  = coe
      MAlonzo.Code.Untyped.C_case_40
      (coe MAlonzo.Code.Untyped.C_error_46)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Untyped.C_ƛ_20
            (coe
               MAlonzo.Code.Untyped.C_case_40
               (coe MAlonzo.Code.Untyped.C_error_46)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Untyped.C_delay_26
                     (coe MAlonzo.Code.Untyped.C_error_46))
                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- VerifiedCompilation.UForceCaseDelay.test4
d_test4_328 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_test4_328 = erased
-- VerifiedCompilation.UForceCaseDelay.fstTest5
d_fstTest5_330 :: Integer -> MAlonzo.Code.Untyped.T__'8866'_14
d_fstTest5_330 ~v0 = du_fstTest5_330
du_fstTest5_330 :: MAlonzo.Code.Untyped.T__'8866'_14
du_fstTest5_330
  = coe
      MAlonzo.Code.Untyped.C_case_40
      (coe MAlonzo.Code.Untyped.C_error_46)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Untyped.C_ƛ_20
            (coe
               MAlonzo.Code.Untyped.C_force_24
               (coe
                  MAlonzo.Code.Untyped.C_case_40
                  (coe MAlonzo.Code.Untyped.C_error_46)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe MAlonzo.Code.Untyped.C_delay_26 (coe du_fstTest1_306))
                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- VerifiedCompilation.UForceCaseDelay.sndTest5
d_sndTest5_332 :: Integer -> MAlonzo.Code.Untyped.T__'8866'_14
d_sndTest5_332 ~v0 = du_sndTest5_332
du_sndTest5_332 :: MAlonzo.Code.Untyped.T__'8866'_14
du_sndTest5_332
  = coe
      MAlonzo.Code.Untyped.C_case_40
      (coe MAlonzo.Code.Untyped.C_error_46)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Untyped.C_ƛ_20
            (coe
               MAlonzo.Code.Untyped.C_case_40
               (coe MAlonzo.Code.Untyped.C_error_46)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe du_sndTest1_308)
                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- VerifiedCompilation.UForceCaseDelay.test5
d_test5_334 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_test5_334 = erased
-- VerifiedCompilation.UForceCaseDelay.fstTest6
d_fstTest6_336 :: Integer -> MAlonzo.Code.Untyped.T__'8866'_14
d_fstTest6_336 ~v0 = du_fstTest6_336
du_fstTest6_336 :: MAlonzo.Code.Untyped.T__'8866'_14
du_fstTest6_336
  = coe
      MAlonzo.Code.Untyped.C_force_24
      (coe
         MAlonzo.Code.Untyped.C_case_40
         (coe MAlonzo.Code.Untyped.C_error_46)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Untyped.C_ƛ_20
               (coe
                  MAlonzo.Code.Untyped.C_delay_26
                  (coe
                     MAlonzo.Code.Untyped.C_force_24
                     (coe
                        MAlonzo.Code.Untyped.C_case_40
                        (coe MAlonzo.Code.Untyped.C_error_46)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe MAlonzo.Code.Untyped.C_delay_26 (coe du_fstTest1_306))
                           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
-- VerifiedCompilation.UForceCaseDelay.sndTest6
d_sndTest6_338 :: Integer -> MAlonzo.Code.Untyped.T__'8866'_14
d_sndTest6_338 ~v0 = du_sndTest6_338
du_sndTest6_338 :: MAlonzo.Code.Untyped.T__'8866'_14
du_sndTest6_338
  = coe
      MAlonzo.Code.Untyped.C_case_40
      (coe MAlonzo.Code.Untyped.C_error_46)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Untyped.C_ƛ_20
            (coe
               MAlonzo.Code.Untyped.C_case_40
               (coe MAlonzo.Code.Untyped.C_error_46)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe du_sndTest1_308)
                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- VerifiedCompilation.UForceCaseDelay.test6
d_test6_340 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_test6_340 = erased
-- VerifiedCompilation.UForceCaseDelay.fstTest7
d_fstTest7_342 :: Integer -> MAlonzo.Code.Untyped.T__'8866'_14
d_fstTest7_342 ~v0 = du_fstTest7_342
du_fstTest7_342 :: MAlonzo.Code.Untyped.T__'8866'_14
du_fstTest7_342
  = coe
      MAlonzo.Code.Untyped.C_force_24
      (coe
         MAlonzo.Code.Untyped.C_case_40
         (coe MAlonzo.Code.Untyped.C_error_46)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Untyped.C_ƛ_20
               (coe
                  MAlonzo.Code.Untyped.C_delay_26
                  (coe
                     MAlonzo.Code.Untyped.C_force_24
                     (coe
                        MAlonzo.Code.Untyped.C_case_40
                        (coe MAlonzo.Code.Untyped.C_error_46)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe MAlonzo.Code.Untyped.C_delay_26 (coe du_fstTest2_312))
                           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
-- VerifiedCompilation.UForceCaseDelay.sndTest7
d_sndTest7_344 :: Integer -> MAlonzo.Code.Untyped.T__'8866'_14
d_sndTest7_344 ~v0 = du_sndTest7_344
du_sndTest7_344 :: MAlonzo.Code.Untyped.T__'8866'_14
du_sndTest7_344
  = coe
      MAlonzo.Code.Untyped.C_case_40
      (coe MAlonzo.Code.Untyped.C_error_46)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Untyped.C_ƛ_20
            (coe
               MAlonzo.Code.Untyped.C_case_40
               (coe MAlonzo.Code.Untyped.C_error_46)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe du_sndTest2_314)
                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- VerifiedCompilation.UForceCaseDelay.test7
d_test7_346 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_test7_346 = erased
