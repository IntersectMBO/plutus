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
import qualified MAlonzo.Code.VerifiedCompilation.Trace

-- VerifiedCompilation.Certificate.CertResult
d_CertResult_12 a0 a1 = ()
data T_CertResult_12
  = C_proof_18 AgdaAny |
    C_ce_26 MAlonzo.Code.VerifiedCompilation.Trace.T_SimplifierTag_4
            AgdaAny AgdaAny |
    C_abort_32 MAlonzo.Code.VerifiedCompilation.Trace.T_SimplifierTag_4
               AgdaAny AgdaAny
-- VerifiedCompilation.Certificate.ProofOrCE
d_ProofOrCE_38 a0 a1 = ()
data T_ProofOrCE_38
  = C_proof_44 AgdaAny |
    C_ce_52 MAlonzo.Code.VerifiedCompilation.Trace.T_SimplifierTag_4
            AgdaAny AgdaAny
-- VerifiedCompilation.Certificate.isProof?
d_isProof'63'_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_ProofOrCE_38 -> Bool
d_isProof'63'_56 ~v0 ~v1 v2 = du_isProof'63'_56 v2
du_isProof'63'_56 :: T_ProofOrCE_38 -> Bool
du_isProof'63'_56 v0
  = case coe v0 of
      C_proof_44 v1 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_ce_52 v4 v5 v6 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.Certificate.isCE?
d_isCE'63'_60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_ProofOrCE_38 -> Bool
d_isCE'63'_60 ~v0 ~v1 v2 = du_isCE'63'_60 v2
du_isCE'63'_60 :: T_ProofOrCE_38 -> Bool
du_isCE'63'_60 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.d_not_22
      (coe du_isProof'63'_56 (coe v0))
-- VerifiedCompilation.Certificate.Proof?
d_Proof'63'_66 a0 a1 = ()
data T_Proof'63'_66
  = C_proof_72 AgdaAny |
    C_abort_78 MAlonzo.Code.VerifiedCompilation.Trace.T_SimplifierTag_4
               AgdaAny AgdaAny
-- VerifiedCompilation.Certificate._>>=_
d__'62''62''61'__88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  T_Proof'63'_66 -> (AgdaAny -> T_Proof'63'_66) -> T_Proof'63'_66
d__'62''62''61'__88 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du__'62''62''61'__88 v4 v5
du__'62''62''61'__88 ::
  T_Proof'63'_66 -> (AgdaAny -> T_Proof'63'_66) -> T_Proof'63'_66
du__'62''62''61'__88 v0 v1
  = case coe v0 of
      C_proof_72 v2 -> coe v1 v2
      C_abort_78 v4 v5 v6 -> coe C_abort_78 v4 v5 v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.Certificate.DecidableCE
d_DecidableCE_108 ::
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> ()
d_DecidableCE_108 = erased
-- VerifiedCompilation.Certificate.Checkable
d_Checkable_126 :: () -> () -> (AgdaAny -> AgdaAny -> ()) -> ()
d_Checkable_126 = erased
-- VerifiedCompilation.Certificate.Certifiable
d_Certifiable_142 :: () -> (AgdaAny -> AgdaAny -> ()) -> ()
d_Certifiable_142 = erased
-- VerifiedCompilation.Certificate.checker
d_checker_156 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> T_Proof'63'_66) ->
  AgdaAny -> AgdaAny -> T_CertResult_12
d_checker_156 ~v0 ~v1 v2 v3 v4 = du_checker_156 v2 v3 v4
du_checker_156 ::
  (AgdaAny -> AgdaAny -> T_Proof'63'_66) ->
  AgdaAny -> AgdaAny -> T_CertResult_12
du_checker_156 v0 v1 v2
  = let v3 = coe v0 v1 v2 in
    coe
      (case coe v3 of
         C_proof_72 v4 -> coe C_proof_18 (coe v4)
         C_abort_78 v6 v7 v8 -> coe C_abort_32 v6 v7 v8
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.Certificate.decider
d_decider_192 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> T_ProofOrCE_38) ->
  AgdaAny -> AgdaAny -> T_CertResult_12
d_decider_192 ~v0 ~v1 v2 v3 v4 = du_decider_192 v2 v3 v4
du_decider_192 ::
  (AgdaAny -> AgdaAny -> T_ProofOrCE_38) ->
  AgdaAny -> AgdaAny -> T_CertResult_12
du_decider_192 v0 v1 v2
  = let v3 = coe v0 v1 v2 in
    coe
      (case coe v3 of
         C_proof_44 v4 -> coe C_proof_18 (coe v4)
         C_ce_52 v7 v8 v9 -> coe C_ce_26 v7 v8 v9
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.Certificate.decToPCE
d_decToPCE_234 ::
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Trace.T_SimplifierTag_4 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny -> T_ProofOrCE_38
d_decToPCE_234 ~v0 ~v1 v2 v3 v4 v5 = du_decToPCE_234 v2 v3 v4 v5
du_decToPCE_234 ::
  MAlonzo.Code.VerifiedCompilation.Trace.T_SimplifierTag_4 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny -> T_ProofOrCE_38
du_decToPCE_234 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then case coe v5 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v6
                      -> coe C_proof_44 (coe v6)
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe seq (coe v5) (coe C_ce_52 v0 v2 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.Certificate.pceToDec
d_pceToDec_248 ::
  () ->
  T_ProofOrCE_38 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_pceToDec_248 ~v0 v1 = du_pceToDec_248 v1
du_pceToDec_248 ::
  T_ProofOrCE_38 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_pceToDec_248 v0
  = case coe v0 of
      C_proof_44 v1
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 (coe v1))
      C_ce_52 v4 v5 v6
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.Certificate.matchOrCE
d_matchOrCE_262 ::
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.VerifiedCompilation.Trace.T_SimplifierTag_4 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny -> AgdaAny -> T_ProofOrCE_38
d_matchOrCE_262 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_matchOrCE_262 v4 v5 v6 v7
du_matchOrCE_262 ::
  MAlonzo.Code.VerifiedCompilation.Trace.T_SimplifierTag_4 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny -> AgdaAny -> T_ProofOrCE_38
du_matchOrCE_262 v0 v1 v2 v3
  = let v4 = coe v1 v2 v3 in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v7
                         -> coe C_proof_44 (coe v7)
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe seq (coe v6) (coe C_ce_52 v0 v2 v3)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.Certificate.pcePointwise
d_pcePointwise_304 ::
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.VerifiedCompilation.Trace.T_SimplifierTag_4 ->
  (AgdaAny -> AgdaAny -> T_ProofOrCE_38) ->
  [AgdaAny] -> [AgdaAny] -> T_ProofOrCE_38
d_pcePointwise_304 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_pcePointwise_304 v4 v5 v6 v7
du_pcePointwise_304 ::
  MAlonzo.Code.VerifiedCompilation.Trace.T_SimplifierTag_4 ->
  (AgdaAny -> AgdaAny -> T_ProofOrCE_38) ->
  [AgdaAny] -> [AgdaAny] -> T_ProofOrCE_38
du_pcePointwise_304 v0 v1 v2 v3
  = case coe v2 of
      []
        -> case coe v3 of
             []
               -> coe
                    C_proof_44
                    (coe
                       MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C_'91''93'_56)
             (:) v4 v5 -> coe C_ce_52 v0 v2 v5
             _ -> MAlonzo.RTE.mazUnreachableError
      (:) v4 v5
        -> case coe v3 of
             [] -> coe C_ce_52 v0 v5 v3
             (:) v6 v7
               -> let v8 = coe v1 v4 v6 in
                  coe
                    (case coe v8 of
                       C_proof_44 v9
                         -> let v10
                                  = coe du_pcePointwise_304 (coe v0) (coe v1) (coe v5) (coe v7) in
                            coe
                              (case coe v10 of
                                 C_proof_44 v11
                                   -> coe
                                        C_proof_44
                                        (coe
                                           MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62
                                           v9 v11)
                                 C_ce_52 v14 v15 v16 -> coe C_ce_52 v14 v15 v16
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       C_ce_52 v12 v13 v14 -> coe C_ce_52 v12 v13 v14
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
