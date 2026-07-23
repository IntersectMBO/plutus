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

module MAlonzo.Code.VerifiedCompilation.Certificate where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects
import qualified MAlonzo.Code.Utils
import qualified MAlonzo.Code.VerifiedCompilation.Trace

-- VerifiedCompilation.Certificate.CertResult
d_CertResult_12 a0 a1 = ()
data T_CertResult_12
  = C_proof_18 AgdaAny |
    C_ce_26 (MAlonzo.Code.Utils.T_Either_6
               MAlonzo.Code.VerifiedCompilation.Trace.T_UncertifiedOptTag_4
               MAlonzo.Code.VerifiedCompilation.Trace.T_CertifiedOptTag_10)
            AgdaAny AgdaAny |
    C_abort_32 (MAlonzo.Code.Utils.T_Either_6
                  MAlonzo.Code.VerifiedCompilation.Trace.T_UncertifiedOptTag_4
                  MAlonzo.Code.VerifiedCompilation.Trace.T_CertifiedOptTag_10)
               AgdaAny AgdaAny
-- VerifiedCompilation.Certificate.is-proof
d_is'45'proof_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_CertResult_12 -> Bool
d_is'45'proof_36 ~v0 ~v1 v2 = du_is'45'proof_36 v2
du_is'45'proof_36 :: T_CertResult_12 -> Bool
du_is'45'proof_36 v0
  = case coe v0 of
      C_proof_18 v1 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_ce_26 v4 v5 v6 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_abort_32 v3 v4 v5 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.Certificate.to-witness-T
d_to'45'witness'45'T_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_CertResult_12 -> AgdaAny -> AgdaAny
d_to'45'witness'45'T_42 ~v0 ~v1 v2 ~v3
  = du_to'45'witness'45'T_42 v2
du_to'45'witness'45'T_42 :: T_CertResult_12 -> AgdaAny
du_to'45'witness'45'T_42 v0
  = case coe v0 of
      C_proof_18 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.Certificate.ProofOrCE
d_ProofOrCE_50 a0 a1 = ()
data T_ProofOrCE_50
  = C_proof_56 AgdaAny |
    C_ce_64 (MAlonzo.Code.Utils.T_Either_6
               MAlonzo.Code.VerifiedCompilation.Trace.T_UncertifiedOptTag_4
               MAlonzo.Code.VerifiedCompilation.Trace.T_CertifiedOptTag_10)
            AgdaAny AgdaAny
-- VerifiedCompilation.Certificate.isProof?
d_isProof'63'_68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_ProofOrCE_50 -> Bool
d_isProof'63'_68 ~v0 ~v1 v2 = du_isProof'63'_68 v2
du_isProof'63'_68 :: T_ProofOrCE_50 -> Bool
du_isProof'63'_68 v0
  = case coe v0 of
      C_proof_56 v1 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_ce_64 v4 v5 v6 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.Certificate.isCE?
d_isCE'63'_72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_ProofOrCE_50 -> Bool
d_isCE'63'_72 ~v0 ~v1 v2 = du_isCE'63'_72 v2
du_isCE'63'_72 :: T_ProofOrCE_50 -> Bool
du_isCE'63'_72 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.d_not_22
      (coe du_isProof'63'_68 (coe v0))
-- VerifiedCompilation.Certificate.Proof?
d_Proof'63'_78 a0 a1 = ()
data T_Proof'63'_78
  = C_proof_84 AgdaAny |
    C_abort_90 (MAlonzo.Code.Utils.T_Either_6
                  MAlonzo.Code.VerifiedCompilation.Trace.T_UncertifiedOptTag_4
                  MAlonzo.Code.VerifiedCompilation.Trace.T_CertifiedOptTag_10)
               AgdaAny AgdaAny
-- VerifiedCompilation.Certificate._>>=_
d__'62''62''61'__100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  T_Proof'63'_78 -> (AgdaAny -> T_Proof'63'_78) -> T_Proof'63'_78
d__'62''62''61'__100 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du__'62''62''61'__100 v4 v5
du__'62''62''61'__100 ::
  T_Proof'63'_78 -> (AgdaAny -> T_Proof'63'_78) -> T_Proof'63'_78
du__'62''62''61'__100 v0 v1
  = case coe v0 of
      C_proof_84 v2 -> coe v1 v2
      C_abort_90 v4 v5 v6 -> coe C_abort_90 v4 v5 v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.Certificate.DecidableCE
d_DecidableCE_120 ::
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> ()
d_DecidableCE_120 = erased
-- VerifiedCompilation.Certificate.Checkable
d_Checkable_138 :: () -> () -> (AgdaAny -> AgdaAny -> ()) -> ()
d_Checkable_138 = erased
-- VerifiedCompilation.Certificate.Certifiable
d_Certifiable_154 :: () -> (AgdaAny -> AgdaAny -> ()) -> ()
d_Certifiable_154 = erased
-- VerifiedCompilation.Certificate.checker
d_checker_168 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> T_Proof'63'_78) ->
  AgdaAny -> AgdaAny -> T_CertResult_12
d_checker_168 ~v0 ~v1 v2 v3 v4 = du_checker_168 v2 v3 v4
du_checker_168 ::
  (AgdaAny -> AgdaAny -> T_Proof'63'_78) ->
  AgdaAny -> AgdaAny -> T_CertResult_12
du_checker_168 v0 v1 v2
  = let v3 = coe v0 v1 v2 in
    coe
      (case coe v3 of
         C_proof_84 v4 -> coe C_proof_18 (coe v4)
         C_abort_90 v6 v7 v8 -> coe C_abort_32 v6 v7 v8
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.Certificate.decider
d_decider_204 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> T_ProofOrCE_50) ->
  AgdaAny -> AgdaAny -> T_CertResult_12
d_decider_204 ~v0 ~v1 v2 v3 v4 = du_decider_204 v2 v3 v4
du_decider_204 ::
  (AgdaAny -> AgdaAny -> T_ProofOrCE_50) ->
  AgdaAny -> AgdaAny -> T_CertResult_12
du_decider_204 v0 v1 v2
  = let v3 = coe v0 v1 v2 in
    coe
      (case coe v3 of
         C_proof_56 v4 -> coe C_proof_18 (coe v4)
         C_ce_64 v7 v8 v9 -> coe C_ce_26 v7 v8 v9
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.Certificate.decider'
d_decider''_242 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.VerifiedCompilation.Trace.T_UncertifiedOptTag_4
    MAlonzo.Code.VerifiedCompilation.Trace.T_CertifiedOptTag_10 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny -> AgdaAny -> T_CertResult_12
d_decider''_242 ~v0 ~v1 v2 v3 v4 v5 = du_decider''_242 v2 v3 v4 v5
du_decider''_242 ::
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.VerifiedCompilation.Trace.T_UncertifiedOptTag_4
    MAlonzo.Code.VerifiedCompilation.Trace.T_CertifiedOptTag_10 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny -> AgdaAny -> T_CertResult_12
du_decider''_242 v0 v1 v2 v3
  = let v4 = coe v1 v2 v3 in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v7
                         -> coe C_proof_18 (coe v7)
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe seq (coe v6) (coe C_ce_26 v0 v2 v3)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.Certificate.decToPCE
d_decToPCE_284 ::
  () ->
  () ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.VerifiedCompilation.Trace.T_UncertifiedOptTag_4
    MAlonzo.Code.VerifiedCompilation.Trace.T_CertifiedOptTag_10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny -> T_ProofOrCE_50
d_decToPCE_284 ~v0 ~v1 v2 v3 v4 v5 = du_decToPCE_284 v2 v3 v4 v5
du_decToPCE_284 ::
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.VerifiedCompilation.Trace.T_UncertifiedOptTag_4
    MAlonzo.Code.VerifiedCompilation.Trace.T_CertifiedOptTag_10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny -> T_ProofOrCE_50
du_decToPCE_284 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then case coe v5 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v6
                      -> coe C_proof_56 (coe v6)
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe seq (coe v5) (coe C_ce_64 v0 v2 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.Certificate.pceToDec
d_pceToDec_298 ::
  () ->
  T_ProofOrCE_50 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_pceToDec_298 ~v0 v1 = du_pceToDec_298 v1
du_pceToDec_298 ::
  T_ProofOrCE_50 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_pceToDec_298 v0
  = case coe v0 of
      C_proof_56 v1
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 (coe v1))
      C_ce_64 v4 v5 v6
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.Certificate.matchOrCE
d_matchOrCE_312 ::
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.VerifiedCompilation.Trace.T_UncertifiedOptTag_4
    MAlonzo.Code.VerifiedCompilation.Trace.T_CertifiedOptTag_10 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny -> AgdaAny -> T_ProofOrCE_50
d_matchOrCE_312 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_matchOrCE_312 v4 v5 v6 v7
du_matchOrCE_312 ::
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.VerifiedCompilation.Trace.T_UncertifiedOptTag_4
    MAlonzo.Code.VerifiedCompilation.Trace.T_CertifiedOptTag_10 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny -> AgdaAny -> T_ProofOrCE_50
du_matchOrCE_312 v0 v1 v2 v3
  = let v4 = coe v1 v2 v3 in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v7
                         -> coe C_proof_56 (coe v7)
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe seq (coe v6) (coe C_ce_64 v0 v2 v3)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.Certificate.pcePointwise
d_pcePointwise_354 ::
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.VerifiedCompilation.Trace.T_UncertifiedOptTag_4
    MAlonzo.Code.VerifiedCompilation.Trace.T_CertifiedOptTag_10 ->
  (AgdaAny -> AgdaAny -> T_ProofOrCE_50) ->
  [AgdaAny] -> [AgdaAny] -> T_ProofOrCE_50
d_pcePointwise_354 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_pcePointwise_354 v4 v5 v6 v7
du_pcePointwise_354 ::
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.VerifiedCompilation.Trace.T_UncertifiedOptTag_4
    MAlonzo.Code.VerifiedCompilation.Trace.T_CertifiedOptTag_10 ->
  (AgdaAny -> AgdaAny -> T_ProofOrCE_50) ->
  [AgdaAny] -> [AgdaAny] -> T_ProofOrCE_50
du_pcePointwise_354 v0 v1 v2 v3
  = case coe v2 of
      []
        -> case coe v3 of
             []
               -> coe
                    C_proof_56
                    (coe
                       MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C_'91''93'_56)
             (:) v4 v5 -> coe C_ce_64 v0 v2 v5
             _ -> MAlonzo.RTE.mazUnreachableError
      (:) v4 v5
        -> case coe v3 of
             [] -> coe C_ce_64 v0 v5 v3
             (:) v6 v7
               -> let v8 = coe v1 v4 v6 in
                  coe
                    (case coe v8 of
                       C_proof_56 v9
                         -> let v10
                                  = coe du_pcePointwise_354 (coe v0) (coe v1) (coe v5) (coe v7) in
                            coe
                              (case coe v10 of
                                 C_proof_56 v11
                                   -> coe
                                        C_proof_56
                                        (coe
                                           MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62
                                           v9 v11)
                                 C_ce_64 v14 v15 v16 -> coe C_ce_64 v14 v15 v16
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       C_ce_64 v12 v13 v14 -> coe C_ce_64 v12 v13 v14
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
