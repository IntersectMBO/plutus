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
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Properties
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
              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_constr'63'_1572
              (coe
                 MAlonzo.Code.Data.Nat.Properties.d__'8799'__2688
                 (coe (0 :: Integer)))
              (coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du__'8759''63'__1910
                 (\ v3 ->
                    coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_1880)
                 (\ v3 ->
                    coe
                      MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_1880)) in
    coe
      (let v4
             = coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du_singleton'63'_1970 in
       coe
         (case coe v2 of
            MAlonzo.Code.Untyped.C_'96'_18 v5
              -> coe
                   MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52
                   (coe MAlonzo.Code.VerifiedCompilation.Trace.C_applyToCaseT_20) v1
                   v2
            MAlonzo.Code.Untyped.C_ƛ_20 v5
              -> coe
                   MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52
                   (coe MAlonzo.Code.VerifiedCompilation.Trace.C_applyToCaseT_20) v1
                   v2
            MAlonzo.Code.Untyped.C__'183'__22 v5 v6
              -> coe
                   MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52
                   (coe MAlonzo.Code.VerifiedCompilation.Trace.C_applyToCaseT_20) v1
                   v2
            MAlonzo.Code.Untyped.C_force_24 v5
              -> coe
                   MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52
                   (coe MAlonzo.Code.VerifiedCompilation.Trace.C_applyToCaseT_20) v1
                   v2
            MAlonzo.Code.Untyped.C_delay_26 v5
              -> coe
                   MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52
                   (coe MAlonzo.Code.VerifiedCompilation.Trace.C_applyToCaseT_20) v1
                   v2
            MAlonzo.Code.Untyped.C_con_28 v5
              -> coe
                   MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52
                   (coe MAlonzo.Code.VerifiedCompilation.Trace.C_applyToCaseT_20) v1
                   v2
            MAlonzo.Code.Untyped.C_constr_34 v5 v6
              -> coe
                   MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52
                   (coe MAlonzo.Code.VerifiedCompilation.Trace.C_applyToCaseT_20) v1
                   v2
            MAlonzo.Code.Untyped.C_case_40 v5 v6
              -> let v7
                       = coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__76
                           (coe v3 v5) (coe v4 v6) in
                 coe
                   (case coe v7 of
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                        -> if coe v8
                             then case coe v9 of
                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v10
                                      -> case coe v10 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                             -> case coe v11 of
                                                  MAlonzo.Code.VerifiedCompilation.UntypedViews.C_constr'33'_954 v15 v16
                                                    -> case coe v5 of
                                                         MAlonzo.Code.Untyped.C_constr_34 v17 v18
                                                           -> case coe v16 of
                                                                MAlonzo.Code.VerifiedCompilation.UntypedViews.C__'8759''33'__1902 v21 v22
                                                                  -> coe
                                                                       seq (coe v21)
                                                                       (coe
                                                                          seq (coe v22)
                                                                          (case coe v12 of
                                                                             MAlonzo.Code.VerifiedCompilation.UntypedViews.C__'8759''33'__1902 v25 v26
                                                                               -> case coe v6 of
                                                                                    (:) v27 v28
                                                                                      -> coe
                                                                                           seq
                                                                                           (coe v25)
                                                                                           (let v29
                                                                                                  = coe
                                                                                                      d_a2c'63''7580''7580'_24
                                                                                                      v0
                                                                                                      v1
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Untyped.Reduction.du_iterApp_242
                                                                                                         (coe
                                                                                                            v27)
                                                                                                         (coe
                                                                                                            v18)) in
                                                                                            coe
                                                                                              (case coe
                                                                                                      v29 of
                                                                                                 MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_44 v30
                                                                                                   -> coe
                                                                                                        MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_44
                                                                                                        (coe
                                                                                                           C_a2c_16
                                                                                                           v30)
                                                                                                 MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52 v33 v34 v35
                                                                                                   -> coe
                                                                                                        MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52
                                                                                                        v33
                                                                                                        v34
                                                                                                        v35
                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                             _ -> MAlonzo.RTE.mazUnreachableError))
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             else (let v10
                                         = seq
                                             (coe v9)
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                (coe v8)
                                                (coe
                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                   coe
                                     (case coe v10 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                          -> if coe v11
                                               then case coe v12 of
                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v13
                                                        -> case coe v13 of
                                                             MAlonzo.Code.VerifiedCompilation.UntypedViews.C_case'33'_936 v16 v17
                                                               -> case coe v16 of
                                                                    MAlonzo.Code.VerifiedCompilation.UntypedViews.C_constr'33'_954 v20 v21
                                                                      -> case coe v5 of
                                                                           MAlonzo.Code.Untyped.C_constr_34 v22 v23
                                                                             -> case coe v21 of
                                                                                  MAlonzo.Code.VerifiedCompilation.UntypedViews.C__'8759''33'__1902 v26 v27
                                                                                    -> coe
                                                                                         seq
                                                                                         (coe v26)
                                                                                         (coe
                                                                                            seq
                                                                                            (coe
                                                                                               v27)
                                                                                            (case coe
                                                                                                    v17 of
                                                                                               MAlonzo.Code.VerifiedCompilation.UntypedViews.C__'8759''33'__1902 v30 v31
                                                                                                 -> case coe
                                                                                                           v6 of
                                                                                                      (:) v32 v33
                                                                                                        -> coe
                                                                                                             seq
                                                                                                             (coe
                                                                                                                v30)
                                                                                                             (let v34
                                                                                                                    = coe
                                                                                                                        d_a2c'63''7580''7580'_24
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Untyped.Reduction.du_iterApp_242
                                                                                                                           (coe
                                                                                                                              v32)
                                                                                                                           (coe
                                                                                                                              v23)) in
                                                                                                              coe
                                                                                                                (case coe
                                                                                                                        v34 of
                                                                                                                   MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_44 v35
                                                                                                                     -> coe
                                                                                                                          MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_44
                                                                                                                          (coe
                                                                                                                             C_a2c_16
                                                                                                                             v35)
                                                                                                                   MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52 v38 v39 v40
                                                                                                                     -> coe
                                                                                                                          MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52
                                                                                                                          v38
                                                                                                                          v39
                                                                                                                          v40
                                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               else coe
                                                      seq (coe v12)
                                                      (coe
                                                         MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52
                                                         (coe
                                                            MAlonzo.Code.VerifiedCompilation.Trace.C_applyToCaseT_20)
                                                         v1 v2)
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                      _ -> MAlonzo.RTE.mazUnreachableError)
            MAlonzo.Code.Untyped.C_builtin_44 v5
              -> coe
                   MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52
                   (coe MAlonzo.Code.VerifiedCompilation.Trace.C_applyToCaseT_20) v1
                   v2
            MAlonzo.Code.Untyped.C_error_46
              -> coe
                   MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52
                   (coe MAlonzo.Code.VerifiedCompilation.Trace.C_applyToCaseT_20) v1
                   v2
            _ -> MAlonzo.RTE.mazUnreachableError))
-- VerifiedCompilation.UApplyToCase..extendedlambda0
d_'46'extendedlambda0_48 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_case'7510'_926 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  T_ApplyToCase_4 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda0_48 = erased
-- VerifiedCompilation.UApplyToCase..extendedlambda1
d_'46'extendedlambda1_94 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Trace.T_SimplifierTag_4 ->
  AgdaAny ->
  AgdaAny ->
  T_ApplyToCase_4 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda1_94 = erased
-- VerifiedCompilation.UApplyToCase.UApplyToCase
d_UApplyToCase_98 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> ()
d_UApplyToCase_98 = erased
