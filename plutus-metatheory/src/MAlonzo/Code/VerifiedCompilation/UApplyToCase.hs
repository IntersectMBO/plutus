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

module MAlonzo.Code.VerifiedCompilation.UApplyToCase where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects
import qualified MAlonzo.Code.Untyped
import qualified MAlonzo.Code.Untyped.Reduction
import qualified MAlonzo.Code.VerifiedCompilation.Certificate
import qualified MAlonzo.Code.VerifiedCompilation.Trace
import qualified MAlonzo.Code.VerifiedCompilation.UntypedTranslation
import qualified MAlonzo.Code.VerifiedCompilation.UntypedViews

-- VerifiedCompilation.UApplyToCase.ApplyToCase
d_ApplyToCase_4 a0 a1 a2 = ()
newtype T_ApplyToCase_4
  = C_a2c_16 MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_12
-- VerifiedCompilation.UApplyToCase.a2c?ᶜᶜ
d_a2c'63''7580''7580'_24 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_38
d_a2c'63''7580''7580'_24 v0
  = coe
      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.du_translation'63'_164
      (coe v0)
      (coe MAlonzo.Code.VerifiedCompilation.Trace.C_applyToCaseT_20)
      (coe d_a2c'63'_32)
-- VerifiedCompilation.UApplyToCase.a2c?
d_a2c'63'_32 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_38
d_a2c'63'_32 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isCase'63'_600
              (coe v0)
              (coe
                 (\ v3 ->
                    coe
                      MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isConstr'63'_498
                      (coe v3)
                      (\ v4 v5 ->
                         coe
                           MAlonzo.Code.VerifiedCompilation.UntypedViews.du_allTerms'63'_800)))
              (\ v3 v4 ->
                 coe
                   MAlonzo.Code.VerifiedCompilation.UntypedViews.du_allTerms'63'_800)
              (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then case coe v5 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v6
                         -> case coe v6 of
                              MAlonzo.Code.VerifiedCompilation.UntypedViews.C_iscase_588 v9 v10
                                -> case coe v2 of
                                     MAlonzo.Code.Untyped.C_case_40 v11 v12
                                       -> case coe v9 of
                                            MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isconstr_490 v15
                                              -> case coe v11 of
                                                   MAlonzo.Code.Untyped.C_constr_34 v16 v17
                                                     -> coe
                                                          seq (coe v15)
                                                          (coe
                                                             seq (coe v10)
                                                             (case coe v16 of
                                                                0 -> case coe v17 of
                                                                       []
                                                                         -> coe
                                                                              MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52
                                                                              (coe
                                                                                 MAlonzo.Code.VerifiedCompilation.Trace.C_applyToCaseT_20)
                                                                              v1 v2
                                                                       (:) v18 v19
                                                                         -> case coe v12 of
                                                                              []
                                                                                -> coe
                                                                                     MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52
                                                                                     (coe
                                                                                        MAlonzo.Code.VerifiedCompilation.Trace.C_applyToCaseT_20)
                                                                                     v1 v2
                                                                              (:) v20 v21
                                                                                -> case coe v21 of
                                                                                     []
                                                                                       -> let v22
                                                                                                = coe
                                                                                                    d_a2c'63''7580''7580'_24
                                                                                                    v0
                                                                                                    v1
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Untyped.Reduction.du_iterApp_242
                                                                                                       (coe
                                                                                                          v20)
                                                                                                       (coe
                                                                                                          v17)) in
                                                                                          coe
                                                                                            (case coe
                                                                                                    v22 of
                                                                                               MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_44 v23
                                                                                                 -> coe
                                                                                                      MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_44
                                                                                                      (coe
                                                                                                         C_a2c_16
                                                                                                         v23)
                                                                                               MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52 v26 v27 v28
                                                                                                 -> coe
                                                                                                      MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52
                                                                                                      v26
                                                                                                      v27
                                                                                                      v28
                                                                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                     (:) v22 v23
                                                                                       -> coe
                                                                                            MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52
                                                                                            (coe
                                                                                               MAlonzo.Code.VerifiedCompilation.Trace.C_applyToCaseT_20)
                                                                                            v1 v2
                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                _ -> coe
                                                                       MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52
                                                                       (coe
                                                                          MAlonzo.Code.VerifiedCompilation.Trace.C_applyToCaseT_20)
                                                                       v1 v2))
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v5)
                       (coe
                          MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52
                          (coe MAlonzo.Code.VerifiedCompilation.Trace.C_applyToCaseT_20) v1
                          v2)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.UApplyToCase..extendedlambda0
d_'46'extendedlambda0_48 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isCase_576 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  T_ApplyToCase_4 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda0_48 = erased
-- VerifiedCompilation.UApplyToCase..extendedlambda1
d_'46'extendedlambda1_206 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Trace.T_SimplifierTag_4 ->
  AgdaAny ->
  AgdaAny ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  Integer ->
  T_ApplyToCase_4 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda1_206 = erased
-- VerifiedCompilation.UApplyToCase.UApplyToCase
d_UApplyToCase_210 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> ()
d_UApplyToCase_210 = erased
