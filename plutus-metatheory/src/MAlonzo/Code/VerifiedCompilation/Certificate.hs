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
-- VerifiedCompilation.Certificate.Proof?
d_Proof'63'_58 a0 a1 = ()
data T_Proof'63'_58
  = C_proof_64 AgdaAny |
    C_abort_70 MAlonzo.Code.VerifiedCompilation.Trace.T_SimplifierTag_4
               AgdaAny AgdaAny
-- VerifiedCompilation.Certificate.Decider
d_Decider_80 ::
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> ()
d_Decider_80 = erased
-- VerifiedCompilation.Certificate.Checker
d_Checker_98 :: () -> () -> (AgdaAny -> AgdaAny -> ()) -> ()
d_Checker_98 = erased
-- VerifiedCompilation.Certificate.Certifier
d_Certifier_118 ::
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> ()
d_Certifier_118 = erased
-- VerifiedCompilation.Certificate.runChecker
d_runChecker_136 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> T_Proof'63'_58) ->
  AgdaAny -> AgdaAny -> T_CertResult_12
d_runChecker_136 ~v0 ~v1 ~v2 v3 v4 v5 = du_runChecker_136 v3 v4 v5
du_runChecker_136 ::
  (AgdaAny -> AgdaAny -> T_Proof'63'_58) ->
  AgdaAny -> AgdaAny -> T_CertResult_12
du_runChecker_136 v0 v1 v2
  = let v3 = coe v0 v1 v2 in
    coe
      (case coe v3 of
         C_proof_64 v4 -> coe C_proof_18 (coe v4)
         C_abort_70 v6 v7 v8 -> coe C_abort_32 v6 v7 v8
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.Certificate.runDecider
d_runDecider_174 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> T_ProofOrCE_38) ->
  AgdaAny -> AgdaAny -> T_CertResult_12
d_runDecider_174 ~v0 ~v1 ~v2 v3 v4 v5 = du_runDecider_174 v3 v4 v5
du_runDecider_174 ::
  (AgdaAny -> AgdaAny -> T_ProofOrCE_38) ->
  AgdaAny -> AgdaAny -> T_CertResult_12
du_runDecider_174 v0 v1 v2
  = let v3 = coe v0 v1 v2 in
    coe
      (case coe v3 of
         C_proof_44 v4 -> coe C_proof_18 (coe v4)
         C_ce_52 v7 v8 v9 -> coe C_ce_26 v7 v8 v9
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.Certificate.decToPCE
d_decToPCE_216 ::
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Trace.T_SimplifierTag_4 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny -> T_ProofOrCE_38
d_decToPCE_216 ~v0 ~v1 v2 v3 v4 v5 = du_decToPCE_216 v2 v3 v4 v5
du_decToPCE_216 ::
  MAlonzo.Code.VerifiedCompilation.Trace.T_SimplifierTag_4 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny -> T_ProofOrCE_38
du_decToPCE_216 v0 v1 v2 v3
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
d_pceToDec_230 ::
  () ->
  T_ProofOrCE_38 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_pceToDec_230 ~v0 v1 = du_pceToDec_230 v1
du_pceToDec_230 ::
  T_ProofOrCE_38 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_pceToDec_230 v0
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
d_matchOrCE_244 ::
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.VerifiedCompilation.Trace.T_SimplifierTag_4 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny -> AgdaAny -> T_ProofOrCE_38
d_matchOrCE_244 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_matchOrCE_244 v4 v5 v6 v7
du_matchOrCE_244 ::
  MAlonzo.Code.VerifiedCompilation.Trace.T_SimplifierTag_4 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny -> AgdaAny -> T_ProofOrCE_38
du_matchOrCE_244 v0 v1 v2 v3
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
d_pcePointwise_286 ::
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.VerifiedCompilation.Trace.T_SimplifierTag_4 ->
  (AgdaAny -> AgdaAny -> T_ProofOrCE_38) ->
  [AgdaAny] -> [AgdaAny] -> T_ProofOrCE_38
d_pcePointwise_286 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_pcePointwise_286 v4 v5 v6 v7
du_pcePointwise_286 ::
  MAlonzo.Code.VerifiedCompilation.Trace.T_SimplifierTag_4 ->
  (AgdaAny -> AgdaAny -> T_ProofOrCE_38) ->
  [AgdaAny] -> [AgdaAny] -> T_ProofOrCE_38
du_pcePointwise_286 v0 v1 v2 v3
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
                                  = coe du_pcePointwise_286 (coe v0) (coe v1) (coe v5) (coe v7) in
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
