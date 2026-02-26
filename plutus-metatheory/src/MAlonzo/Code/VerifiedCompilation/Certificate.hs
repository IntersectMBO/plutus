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
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

import UntypedPlutusCore.Transform.Certify.Trace
import qualified UntypedPlutusCore.Transform.Certify.Hints as Hints
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
-- VerifiedCompilation.Certificate.InlineHints
d_InlineHints_20 = ()
type T_InlineHints_20 = Hints.Inline
pattern C_var_22 = Hints.InlVar
pattern C_expand_24 a0 = Hints.InlExpand a0
pattern C_ƛ_26 a0 = Hints.InlLam a0
pattern C_ƛ'8595'_28 a0 = Hints.InlLamDrop a0
pattern C__'183'__30 a0 a1 = Hints.InlApply a0 a1
pattern C__'183''8595'_32 a0 = Hints.InlDrop a0
pattern C_force_34 a0 = Hints.InlForce a0
pattern C_delay_36 a0 = Hints.InlDelay a0
pattern C_con_38 = Hints.InlCon
pattern C_builtin_40 = Hints.InlBuiltin
pattern C_error_42 = Hints.InlError
pattern C_constr_44 a0 = Hints.InlConstr a0
pattern C_case_46 a0 a1 = Hints.InlCase a0 a1
check_var_22 :: T_InlineHints_20
check_var_22 = Hints.InlVar
check_expand_24 :: T_InlineHints_20 -> T_InlineHints_20
check_expand_24 = Hints.InlExpand
check_ƛ_26 :: T_InlineHints_20 -> T_InlineHints_20
check_ƛ_26 = Hints.InlLam
check_ƛ'8595'_28 :: T_InlineHints_20 -> T_InlineHints_20
check_ƛ'8595'_28 = Hints.InlLamDrop
check__'183'__30 ::
  T_InlineHints_20 -> T_InlineHints_20 -> T_InlineHints_20
check__'183'__30 = Hints.InlApply
check__'183''8595'_32 :: T_InlineHints_20 -> T_InlineHints_20
check__'183''8595'_32 = Hints.InlDrop
check_force_34 :: T_InlineHints_20 -> T_InlineHints_20
check_force_34 = Hints.InlForce
check_delay_36 :: T_InlineHints_20 -> T_InlineHints_20
check_delay_36 = Hints.InlDelay
check_con_38 :: T_InlineHints_20
check_con_38 = Hints.InlCon
check_builtin_40 :: T_InlineHints_20
check_builtin_40 = Hints.InlBuiltin
check_error_42 :: T_InlineHints_20
check_error_42 = Hints.InlError
check_constr_44 ::
  MAlonzo.Code.Agda.Builtin.List.T_List_10 () T_InlineHints_20 ->
  T_InlineHints_20
check_constr_44 = Hints.InlConstr
check_case_46 ::
  T_InlineHints_20 ->
  MAlonzo.Code.Agda.Builtin.List.T_List_10 () T_InlineHints_20 ->
  T_InlineHints_20
check_case_46 = Hints.InlCase
cover_InlineHints_20 :: Hints.Inline -> ()
cover_InlineHints_20 x
  = case x of
      Hints.InlVar -> ()
      Hints.InlExpand _ -> ()
      Hints.InlLam _ -> ()
      Hints.InlLamDrop _ -> ()
      Hints.InlApply _ _ -> ()
      Hints.InlDrop _ -> ()
      Hints.InlForce _ -> ()
      Hints.InlDelay _ -> ()
      Hints.InlCon -> ()
      Hints.InlBuiltin -> ()
      Hints.InlError -> ()
      Hints.InlConstr _ -> ()
      Hints.InlCase _ _ -> ()
-- VerifiedCompilation.Certificate.Hints
d_Hints_48 = ()
type T_Hints_48 = Hints.Hints
pattern C_inline_50 a0 = Hints.Inline a0
pattern C_none_52 = Hints.NoHints
check_inline_50 :: T_InlineHints_20 -> T_Hints_48
check_inline_50 = Hints.Inline
check_none_52 :: T_Hints_48
check_none_52 = Hints.NoHints
cover_Hints_48 :: Hints.Hints -> ()
cover_Hints_48 x
  = case x of
      Hints.Inline _ -> ()
      Hints.NoHints -> ()
-- VerifiedCompilation.Certificate.CertResult
d_CertResult_62 a0 a1 = ()
data T_CertResult_62
  = C_proof_68 AgdaAny | C_ce_76 T_SimplifierTag_4 AgdaAny AgdaAny |
    C_abort_82 T_SimplifierTag_4 AgdaAny AgdaAny
-- VerifiedCompilation.Certificate.ProofOrCE
d_ProofOrCE_88 a0 a1 = ()
data T_ProofOrCE_88
  = C_proof_94 AgdaAny | C_ce_102 T_SimplifierTag_4 AgdaAny AgdaAny
-- VerifiedCompilation.Certificate.Proof?
d_Proof'63'_108 a0 a1 = ()
data T_Proof'63'_108
  = C_proof_114 AgdaAny |
    C_abort_120 T_SimplifierTag_4 AgdaAny AgdaAny
-- VerifiedCompilation.Certificate._>>=_
d__'62''62''61'__130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  T_Proof'63'_108 -> (AgdaAny -> T_Proof'63'_108) -> T_Proof'63'_108
d__'62''62''61'__130 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du__'62''62''61'__130 v4 v5
du__'62''62''61'__130 ::
  T_Proof'63'_108 -> (AgdaAny -> T_Proof'63'_108) -> T_Proof'63'_108
du__'62''62''61'__130 v0 v1
  = case coe v0 of
      C_proof_114 v2 -> coe v1 v2
      C_abort_120 v4 v5 v6 -> coe C_abort_120 v4 v5 v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.Certificate.decToPCE
d_decToPCE_150 ::
  () ->
  () ->
  T_SimplifierTag_4 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny -> T_ProofOrCE_88
d_decToPCE_150 ~v0 ~v1 v2 v3 v4 v5 = du_decToPCE_150 v2 v3 v4 v5
du_decToPCE_150 ::
  T_SimplifierTag_4 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny -> T_ProofOrCE_88
du_decToPCE_150 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then case coe v5 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v6
                      -> coe C_proof_94 (coe v6)
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe seq (coe v5) (coe C_ce_102 v0 v2 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.Certificate.pceToDec
d_pceToDec_164 ::
  () ->
  T_ProofOrCE_88 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_pceToDec_164 ~v0 v1 = du_pceToDec_164 v1
du_pceToDec_164 ::
  T_ProofOrCE_88 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_pceToDec_164 v0
  = case coe v0 of
      C_proof_94 v1
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 (coe v1))
      C_ce_102 v4 v5 v6
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.Certificate.MatchOrCE
d_MatchOrCE_178 ::
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> ()
d_MatchOrCE_178 = erased
-- VerifiedCompilation.Certificate.matchOrCE
d_matchOrCE_198 ::
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_SimplifierTag_4 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny -> AgdaAny -> T_ProofOrCE_88
d_matchOrCE_198 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_matchOrCE_198 v4 v5 v6 v7
du_matchOrCE_198 ::
  T_SimplifierTag_4 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny -> AgdaAny -> T_ProofOrCE_88
du_matchOrCE_198 v0 v1 v2 v3
  = let v4 = coe v1 v2 v3 in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v7
                         -> coe C_proof_94 (coe v7)
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe seq (coe v6) (coe C_ce_102 v0 v2 v3)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.Certificate.pcePointwise
d_pcePointwise_240 ::
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_SimplifierTag_4 ->
  (AgdaAny -> AgdaAny -> T_ProofOrCE_88) ->
  [AgdaAny] -> [AgdaAny] -> T_ProofOrCE_88
d_pcePointwise_240 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_pcePointwise_240 v4 v5 v6 v7
du_pcePointwise_240 ::
  T_SimplifierTag_4 ->
  (AgdaAny -> AgdaAny -> T_ProofOrCE_88) ->
  [AgdaAny] -> [AgdaAny] -> T_ProofOrCE_88
du_pcePointwise_240 v0 v1 v2 v3
  = case coe v2 of
      []
        -> case coe v3 of
             []
               -> coe
                    C_proof_94
                    (coe
                       MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C_'91''93'_56)
             (:) v4 v5 -> coe C_ce_102 v0 v2 v5
             _ -> MAlonzo.RTE.mazUnreachableError
      (:) v4 v5
        -> case coe v3 of
             [] -> coe C_ce_102 v0 v5 v3
             (:) v6 v7
               -> let v8 = coe v1 v4 v6 in
                  coe
                    (case coe v8 of
                       C_proof_94 v9
                         -> let v10
                                  = coe du_pcePointwise_240 (coe v0) (coe v1) (coe v5) (coe v7) in
                            coe
                              (case coe v10 of
                                 C_proof_94 v11
                                   -> coe
                                        C_proof_94
                                        (coe
                                           MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62
                                           v9 v11)
                                 C_ce_102 v14 v15 v16 -> coe C_ce_102 v14 v15 v16
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       C_ce_102 v12 v13 v14 -> coe C_ce_102 v12 v13 v14
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
