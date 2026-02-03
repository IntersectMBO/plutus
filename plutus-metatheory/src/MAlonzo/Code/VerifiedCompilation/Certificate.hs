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

import UntypedPlutusCore.Transform.Simplifier
-- VerifiedCompilation.Certificate.SimplifierTag
d_SimplifierTag_4 = ()
type T_SimplifierTag_4 = SimplifierStage
pattern C_floatDelayT_6 = FloatDelay
pattern C_forceDelayT_8 = ForceDelay
pattern C_forceCaseDelayT_10 = ForceCaseDelay
pattern C_caseOfCaseT_12 = CaseOfCase
pattern C_caseReduceT_14 = CaseReduce
pattern C_inlineT_16 = Inline
pattern C_cseT_18 = CSE
check_floatDelayT_6 :: T_SimplifierTag_4
check_floatDelayT_6 = FloatDelay
check_forceDelayT_8 :: T_SimplifierTag_4
check_forceDelayT_8 = ForceDelay
check_forceCaseDelayT_10 :: T_SimplifierTag_4
check_forceCaseDelayT_10 = ForceCaseDelay
check_caseOfCaseT_12 :: T_SimplifierTag_4
check_caseOfCaseT_12 = CaseOfCase
check_caseReduceT_14 :: T_SimplifierTag_4
check_caseReduceT_14 = CaseReduce
check_inlineT_16 :: T_SimplifierTag_4
check_inlineT_16 = Inline
check_cseT_18 :: T_SimplifierTag_4
check_cseT_18 = CSE
cover_SimplifierTag_4 :: SimplifierStage -> ()
cover_SimplifierTag_4 x
  = case x of
      FloatDelay -> ()
      ForceDelay -> ()
      ForceCaseDelay -> ()
      CaseOfCase -> ()
      CaseReduce -> ()
      Inline -> ()
      CSE -> ()
-- VerifiedCompilation.Certificate.CertResult
d_CertResult_28 a0 a1 = ()
data T_CertResult_28
  = C_proof_34 AgdaAny | C_ce_42 T_SimplifierTag_4 AgdaAny AgdaAny |
    C_abort_48 T_SimplifierTag_4 AgdaAny AgdaAny
-- VerifiedCompilation.Certificate.ProofOrCE
d_ProofOrCE_54 a0 a1 = ()
data T_ProofOrCE_54
  = C_proof_60 AgdaAny | C_ce_68 T_SimplifierTag_4 AgdaAny AgdaAny
-- VerifiedCompilation.Certificate.Proof?
d_Proof'63'_74 a0 a1 = ()
data T_Proof'63'_74
  = C_proof_80 AgdaAny | C_abort_86 T_SimplifierTag_4 AgdaAny AgdaAny
-- VerifiedCompilation.Certificate.decToPCE
d_decToPCE_96 ::
  () ->
  () ->
  T_SimplifierTag_4 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny -> T_ProofOrCE_54
d_decToPCE_96 ~v0 ~v1 v2 v3 v4 v5 = du_decToPCE_96 v2 v3 v4 v5
du_decToPCE_96 ::
  T_SimplifierTag_4 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny -> T_ProofOrCE_54
du_decToPCE_96 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then case coe v5 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v6
                      -> coe C_proof_60 (coe v6)
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe seq (coe v5) (coe C_ce_68 v0 v2 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.Certificate.pceToDec
d_pceToDec_110 ::
  () ->
  T_ProofOrCE_54 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_pceToDec_110 ~v0 v1 = du_pceToDec_110 v1
du_pceToDec_110 ::
  T_ProofOrCE_54 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_pceToDec_110 v0
  = case coe v0 of
      C_proof_60 v1
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 (coe v1))
      C_ce_68 v4 v5 v6
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.Certificate.MatchOrCE
d_MatchOrCE_124 ::
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> ()
d_MatchOrCE_124 = erased
-- VerifiedCompilation.Certificate.matchOrCE
d_matchOrCE_144 ::
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_SimplifierTag_4 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny -> AgdaAny -> T_ProofOrCE_54
d_matchOrCE_144 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_matchOrCE_144 v4 v5 v6 v7
du_matchOrCE_144 ::
  T_SimplifierTag_4 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny -> AgdaAny -> T_ProofOrCE_54
du_matchOrCE_144 v0 v1 v2 v3
  = let v4 = coe v1 v2 v3 in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v7
                         -> coe C_proof_60 (coe v7)
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe seq (coe v6) (coe C_ce_68 v0 v2 v3)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.Certificate.pcePointwise
d_pcePointwise_186 ::
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_SimplifierTag_4 ->
  (AgdaAny -> AgdaAny -> T_ProofOrCE_54) ->
  [AgdaAny] -> [AgdaAny] -> T_ProofOrCE_54
d_pcePointwise_186 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_pcePointwise_186 v4 v5 v6 v7
du_pcePointwise_186 ::
  T_SimplifierTag_4 ->
  (AgdaAny -> AgdaAny -> T_ProofOrCE_54) ->
  [AgdaAny] -> [AgdaAny] -> T_ProofOrCE_54
du_pcePointwise_186 v0 v1 v2 v3
  = case coe v2 of
      []
        -> case coe v3 of
             []
               -> coe
                    C_proof_60
                    (coe
                       MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C_'91''93'_56)
             (:) v4 v5 -> coe C_ce_68 v0 v2 v5
             _ -> MAlonzo.RTE.mazUnreachableError
      (:) v4 v5
        -> case coe v3 of
             [] -> coe C_ce_68 v0 v5 v3
             (:) v6 v7
               -> let v8 = coe v1 v4 v6 in
                  coe
                    (case coe v8 of
                       C_proof_60 v9
                         -> let v10
                                  = coe du_pcePointwise_186 (coe v0) (coe v1) (coe v5) (coe v7) in
                            coe
                              (case coe v10 of
                                 C_proof_60 v11
                                   -> coe
                                        C_proof_60
                                        (coe
                                           MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62
                                           v9 v11)
                                 C_ce_68 v14 v15 v16 -> coe C_ce_68 v14 v15 v16
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       C_ce_68 v12 v13 v14 -> coe C_ce_68 v12 v13 v14
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
