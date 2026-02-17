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
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects
import qualified MAlonzo.Code.Untyped
import qualified MAlonzo.Code.Untyped.Equality
import qualified MAlonzo.Code.VerifiedCompilation.Certificate
import qualified MAlonzo.Code.VerifiedCompilation.UntypedTranslation
import qualified MAlonzo.Code.VerifiedCompilation.UntypedViews

-- VerifiedCompilation.UForceCaseDelay.IsBranch
d_IsBranch_14 a0 a1 = ()
data T_IsBranch_14 = C_B'45'delay_16 | C_B'45'ƛ_18 T_IsBranch_14
-- VerifiedCompilation.UForceCaseDelay.isBranch?
d_isBranch'63'_22 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_isBranch'63'_22 ~v0 v1 = du_isBranch'63'_22 v1
du_isBranch'63'_22 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_isBranch'63'_22 v0
  = case coe v0 of
      MAlonzo.Code.Untyped.C_'96'_18 v1
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      MAlonzo.Code.Untyped.C_ƛ_20 v1
        -> let v2 = coe du_isBranch'63'_22 (coe v1) in
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
                                        (coe C_B'45'ƛ_18 v5))
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
                (coe C_B'45'delay_16))
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
d_removeDelay_64 ::
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14]
d_removeDelay_64 ~v0 v1 = du_removeDelay_64 v1
du_removeDelay_64 ::
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14]
du_removeDelay_64 v0
  = coe MAlonzo.Code.Data.List.Base.du_map_22 (coe du_go_72) (coe v0)
-- VerifiedCompilation.UForceCaseDelay._.go
d_go_72 ::
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14
d_go_72 ~v0 ~v1 ~v2 v3 = du_go_72 v3
du_go_72 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14
du_go_72 v0
  = case coe v0 of
      MAlonzo.Code.Untyped.C_ƛ_20 v1
        -> coe MAlonzo.Code.Untyped.C_ƛ_20 (coe du_go_72 (coe v1))
      MAlonzo.Code.Untyped.C_delay_26 v1 -> coe v1
      _ -> coe v0
-- VerifiedCompilation.UForceCaseDelay.FCD
d_FCD_80 a0 a1 a2 = ()
newtype T_FCD_80
  = C_isFCD_82 MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
-- VerifiedCompilation.UForceCaseDelay.isFCD?
d_isFCD'63'_84 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_86
d_isFCD'63'_84 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isForce'63'_284
              (coe v0)
              (coe
                 (\ v3 ->
                    coe
                      MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isCase'63'_598
                      (coe v3)
                      (\ v4 v5 ->
                         coe
                           MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)
                      (\ v4 v5 ->
                         coe
                           MAlonzo.Code.VerifiedCompilation.UntypedViews.du_allTerms'63'_798)))
              (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then case coe v5 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v6
                         -> case coe v6 of
                              MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isforce_276 v8
                                -> case coe v1 of
                                     MAlonzo.Code.Untyped.C_force_24 v9
                                       -> case coe v8 of
                                            MAlonzo.Code.VerifiedCompilation.UntypedViews.C_iscase_586 v12 v13
                                              -> case coe v9 of
                                                   MAlonzo.Code.Untyped.C_case_40 v14 v15
                                                     -> coe
                                                          seq (coe v12)
                                                          (coe
                                                             seq (coe v13)
                                                             (let v16
                                                                    = coe
                                                                        MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isCase'63'_598
                                                                        (coe v0)
                                                                        (\ v16 v17 ->
                                                                           coe
                                                                             MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)
                                                                        (\ v16 v17 ->
                                                                           coe
                                                                             MAlonzo.Code.VerifiedCompilation.UntypedViews.du_allTerms'63'_798)
                                                                        (coe v2) in
                                                              coe
                                                                (case coe v16 of
                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                     -> if coe v17
                                                                          then case coe v18 of
                                                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v19
                                                                                   -> case coe
                                                                                             v19 of
                                                                                        MAlonzo.Code.VerifiedCompilation.UntypedViews.C_iscase_586 v22 v23
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
                                                                                                                = MAlonzo.Code.Untyped.Equality.d_decEq'45''8866'_52
                                                                                                                    (coe
                                                                                                                       v0)
                                                                                                                    (coe
                                                                                                                       v14)
                                                                                                                    (coe
                                                                                                                       v24) in
                                                                                                          coe
                                                                                                            (case coe
                                                                                                                    v26 of
                                                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v27 v28
                                                                                                                 -> if coe
                                                                                                                         v27
                                                                                                                      then coe
                                                                                                                             seq
                                                                                                                             (coe
                                                                                                                                v28)
                                                                                                                             (let v29
                                                                                                                                    = coe
                                                                                                                                        MAlonzo.Code.Data.List.Properties.du_'8801''45'dec_58
                                                                                                                                        (coe
                                                                                                                                           MAlonzo.Code.Untyped.Equality.d__'8799'__12
                                                                                                                                           (coe
                                                                                                                                              MAlonzo.Code.Untyped.Equality.d_DecEq'45''8866'_146
                                                                                                                                              (coe
                                                                                                                                                 v0)))
                                                                                                                                        (coe
                                                                                                                                           v25)
                                                                                                                                        (coe
                                                                                                                                           du_removeDelay_64
                                                                                                                                           (coe
                                                                                                                                              v15)) in
                                                                                                                              coe
                                                                                                                                (case coe
                                                                                                                                        v29 of
                                                                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v30 v31
                                                                                                                                     -> if coe
                                                                                                                                             v30
                                                                                                                                          then coe
                                                                                                                                                 seq
                                                                                                                                                 (coe
                                                                                                                                                    v31)
                                                                                                                                                 (let v32
                                                                                                                                                        = coe
                                                                                                                                                            MAlonzo.Code.Data.List.Relation.Unary.All.du_all'63'_506
                                                                                                                                                            (coe
                                                                                                                                                               du_isBranch'63'_22)
                                                                                                                                                            (coe
                                                                                                                                                               v15) in
                                                                                                                                                  coe
                                                                                                                                                    (case coe
                                                                                                                                                            v32 of
                                                                                                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v33 v34
                                                                                                                                                         -> if coe
                                                                                                                                                                 v33
                                                                                                                                                              then case coe
                                                                                                                                                                          v34 of
                                                                                                                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v35
                                                                                                                                                                       -> coe
                                                                                                                                                                            MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_92
                                                                                                                                                                            (coe
                                                                                                                                                                               C_isFCD_82
                                                                                                                                                                               v35)
                                                                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                              else coe
                                                                                                                                                                     seq
                                                                                                                                                                     (coe
                                                                                                                                                                        v34)
                                                                                                                                                                     (coe
                                                                                                                                                                        MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_100
                                                                                                                                                                        (coe
                                                                                                                                                                           MAlonzo.Code.VerifiedCompilation.Certificate.C_forceCaseDelayT_10)
                                                                                                                                                                        v1
                                                                                                                                                                        v2)
                                                                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                          else coe
                                                                                                                                                 seq
                                                                                                                                                 (coe
                                                                                                                                                    v31)
                                                                                                                                                 (coe
                                                                                                                                                    MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_100
                                                                                                                                                    (coe
                                                                                                                                                       MAlonzo.Code.VerifiedCompilation.Certificate.C_forceCaseDelayT_10)
                                                                                                                                                    v1
                                                                                                                                                    v2)
                                                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                      else coe
                                                                                                                             seq
                                                                                                                             (coe
                                                                                                                                v28)
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_100
                                                                                                                                (coe
                                                                                                                                   MAlonzo.Code.VerifiedCompilation.Certificate.C_forceCaseDelayT_10)
                                                                                                                                v1
                                                                                                                                v2)
                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError)))
                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                          else coe
                                                                                 seq (coe v18)
                                                                                 (coe
                                                                                    MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_100
                                                                                    (coe
                                                                                       MAlonzo.Code.VerifiedCompilation.Certificate.C_forceCaseDelayT_10)
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
                          MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_100
                          (coe
                             MAlonzo.Code.VerifiedCompilation.Certificate.C_forceCaseDelayT_10)
                          v1 v2)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.UForceCaseDelay.ForceCaseDelay
d_ForceCaseDelay_262 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> ()
d_ForceCaseDelay_262 = erased
-- VerifiedCompilation.UForceCaseDelay.isForceCaseDelay?
d_isForceCaseDelay'63'_264 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_86
d_isForceCaseDelay'63'_264 v0
  = coe
      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.du_translation'63'_164
      (coe v0)
      (coe
         MAlonzo.Code.VerifiedCompilation.Certificate.C_forceCaseDelayT_10)
      (coe d_isFCD'63'_84)
