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

module MAlonzo.Code.VerifiedCompilation.UCaseReduce.Inductive where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base
import qualified MAlonzo.Code.RawU
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects
import qualified MAlonzo.Code.Untyped
import qualified MAlonzo.Code.Untyped.CEK
import qualified MAlonzo.Code.Untyped.Reduction
import qualified MAlonzo.Code.VerifiedCompilation.Certificate
import qualified MAlonzo.Code.VerifiedCompilation.Trace
import qualified MAlonzo.Code.VerifiedCompilation.UntypedTranslation
import qualified MAlonzo.Code.VerifiedCompilation.UntypedViews

-- VerifiedCompilation.UCaseReduce.Inductive.CaseReduce
d_CaseReduce_6 a0 a1 a2 = ()
data T_CaseReduce_6
  = C_casereduce_20 MAlonzo.Code.Untyped.T__'8866'_14
                    MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_8
-- VerifiedCompilation.UCaseReduce.Inductive.isCaseReduce?
d_isCaseReduce'63'_28 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_38
d_isCaseReduce'63'_28 v0
  = coe
      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.du_translation'63'_160
      (coe v0)
      (coe MAlonzo.Code.VerifiedCompilation.Trace.C_caseReduceT_14)
      (coe d_isCR'63'_44)
-- VerifiedCompilation.UCaseReduce.Inductive.justEq
d_justEq_36 ::
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_justEq_36 = erased
-- VerifiedCompilation.UCaseReduce.Inductive.isCR?
d_isCR'63'_44 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_38
d_isCR'63'_44 v0 v1 v2
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
              (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then case coe v5 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v6
                         -> case coe v6 of
                              MAlonzo.Code.VerifiedCompilation.UntypedViews.C_iscase_588 v9 v10
                                -> case coe v1 of
                                     MAlonzo.Code.Untyped.C_case_40 v11 v12
                                       -> case coe v9 of
                                            MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isconstr_490 v15
                                              -> case coe v11 of
                                                   MAlonzo.Code.Untyped.C_constr_34 v16 v17
                                                     -> coe
                                                          seq (coe v15)
                                                          (coe
                                                             seq (coe v10)
                                                             (let v18
                                                                    = coe
                                                                        MAlonzo.Code.Untyped.CEK.du_lookup'63'_996
                                                                        (coe v16) (coe v12) in
                                                              coe
                                                                (case coe v18 of
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v19
                                                                     -> let v20
                                                                              = coe
                                                                                  d_isCaseReduce'63'_28
                                                                                  v0
                                                                                  (coe
                                                                                     MAlonzo.Code.Untyped.Reduction.du_iterApp_242
                                                                                     (coe v19)
                                                                                     (coe v17))
                                                                                  v2 in
                                                                        coe
                                                                          (case coe v20 of
                                                                             MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_44 v21
                                                                               -> coe
                                                                                    MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_44
                                                                                    (coe
                                                                                       C_casereduce_20
                                                                                       v19 v21)
                                                                             MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52 v24 v25 v26
                                                                               -> coe
                                                                                    MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52
                                                                                    v24 v25 v26
                                                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                     -> coe
                                                                          MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52
                                                                          (coe
                                                                             MAlonzo.Code.VerifiedCompilation.Trace.C_caseReduceT_14)
                                                                          v1 v2
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
                          (coe MAlonzo.Code.VerifiedCompilation.Trace.C_caseReduceT_14) v1
                          v2)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.UCaseReduce.Inductive..extendedlambda0
d_'46'extendedlambda0_60 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isCase_576 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  T_CaseReduce_6 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda0_60 = erased
-- VerifiedCompilation.UCaseReduce.Inductive..extendedlambda1
d_'46'extendedlambda1_88 ::
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  T_CaseReduce_6 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda1_88 = erased
-- VerifiedCompilation.UCaseReduce.Inductive..extendedlambda2
d_'46'extendedlambda2_92 ::
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda2_92 = erased
-- VerifiedCompilation.UCaseReduce.Inductive..extendedlambda3
d_'46'extendedlambda3_144 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_8 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Trace.T_SimplifierTag_4 ->
  AgdaAny ->
  AgdaAny ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_CaseReduce_6 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda3_144 = erased
-- VerifiedCompilation.UCaseReduce.Inductive.UCaseReduce
d_UCaseReduce_152 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> ()
d_UCaseReduce_152 = erased
-- VerifiedCompilation.UCaseReduce.Inductive.ast₁
d_ast'8321'_154 :: MAlonzo.Code.Untyped.T__'8866'_14
d_ast'8321'_154
  = coe
      MAlonzo.Code.Untyped.C_case_40
      (coe
         MAlonzo.Code.Untyped.C_constr_34 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
            (coe
               MAlonzo.Code.Untyped.du_con'45'integer_330 (coe (99 :: Integer)))))
      (coe
         MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
         (coe
            MAlonzo.Code.Untyped.C_'96'_18
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- VerifiedCompilation.UCaseReduce.Inductive.ast₁'
d_ast'8321'''_156 :: MAlonzo.Code.Untyped.T__'8866'_14
d_ast'8321'''_156
  = coe
      MAlonzo.Code.Untyped.C__'183'__22
      (coe
         MAlonzo.Code.Untyped.C_'96'_18
         (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
      (coe
         MAlonzo.Code.Untyped.du_con'45'integer_330 (coe (99 :: Integer)))
-- VerifiedCompilation.UCaseReduce.Inductive.ast
d_ast_160 :: MAlonzo.Code.Untyped.T__'8866'_14
d_ast_160
  = coe
      MAlonzo.Code.Untyped.C_case_40
      (coe
         MAlonzo.Code.Untyped.C_constr_34 (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Untyped.du_con'45'integer_330 (coe (12 :: Integer)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Untyped.du_con'45'integer_330 (coe (42 :: Integer)))
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Untyped.C_ƛ_20
            (coe
               MAlonzo.Code.Untyped.C_ƛ_20
               (coe
                  MAlonzo.Code.Untyped.C_'96'_18
                  (coe
                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Untyped.C_ƛ_20
               (coe
                  MAlonzo.Code.Untyped.C_ƛ_20
                  (coe
                     MAlonzo.Code.Untyped.C_case_40
                     (coe
                        MAlonzo.Code.Untyped.C_constr_34 (coe (0 :: Integer))
                        (coe
                           MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                           (coe
                              MAlonzo.Code.Untyped.du_con'45'integer_330 (coe (99 :: Integer)))))
                     (coe
                        MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                        (coe
                           MAlonzo.Code.Untyped.C_'96'_18
                           (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
-- VerifiedCompilation.UCaseReduce.Inductive.ast'
d_ast''_162 :: MAlonzo.Code.Untyped.T__'8866'_14
d_ast''_162
  = coe
      MAlonzo.Code.Untyped.C__'183'__22
      (coe
         MAlonzo.Code.Untyped.du_con'45'integer_330 (coe (42 :: Integer)))
      (coe
         MAlonzo.Code.Untyped.du_con'45'integer_330 (coe (99 :: Integer)))
-- VerifiedCompilation.UCaseReduce.Inductive.conInt
d_conInt_164 :: Integer -> MAlonzo.Code.Untyped.T__'8866'_14
d_conInt_164 v0
  = coe
      MAlonzo.Code.Untyped.C_con_28
      (coe
         MAlonzo.Code.RawU.C_tmCon_206
         (coe
            MAlonzo.Code.RawU.du_tag2TyTag_232
            (coe MAlonzo.Code.RawU.C_integer_30))
         (coe v0))
-- VerifiedCompilation.UCaseReduce.Inductive.does
d_does_170 ::
  () ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_38 -> Bool
d_does_170 ~v0 v1 = du_does_170 v1
du_does_170 ::
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_38 -> Bool
du_does_170 v0
  = case coe v0 of
      MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_44 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52 v4 v5 v6
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.UCaseReduce.Inductive.witness
d_witness_176 ::
  () ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_38 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_witness_176 ~v0 v1 ~v2 = du_witness_176 v1
du_witness_176 ::
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_38 ->
  AgdaAny
du_witness_176 v0
  = case coe v0 of
      MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_44 v1
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.UCaseReduce.Inductive.¬witness
d_'172'witness_184 ::
  () ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_38 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'172'witness_184 = erased
-- VerifiedCompilation.UCaseReduce.Inductive.Ex.M
d_M_190 :: MAlonzo.Code.Untyped.T__'8866'_14
d_M_190
  = coe
      MAlonzo.Code.Untyped.C_case_40
      (coe
         MAlonzo.Code.Untyped.C_constr_34 (coe (0 :: Integer))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Untyped.C_constr_34 (coe (0 :: Integer))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Untyped.C_constr_34 (coe (1 :: Integer))
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
-- VerifiedCompilation.UCaseReduce.Inductive.Ex.M'
d_M''_192 :: MAlonzo.Code.Untyped.T__'8866'_14
d_M''_192
  = coe
      MAlonzo.Code.Untyped.C_constr_34 (coe (0 :: Integer))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- VerifiedCompilation.UCaseReduce.Inductive.Ex.N
d_N_196 :: MAlonzo.Code.Untyped.T__'8866'_14
d_N_196
  = coe
      MAlonzo.Code.Untyped.C_case_40 (coe d_M_190)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Untyped.C_constr_34 (coe (42 :: Integer))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- VerifiedCompilation.UCaseReduce.Inductive.Ex.N'
d_N''_198 :: MAlonzo.Code.Untyped.T__'8866'_14
d_N''_198
  = coe
      MAlonzo.Code.Untyped.C_constr_34 (coe (42 :: Integer))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- VerifiedCompilation.UCaseReduce.Inductive.Ex.problem
d_problem_200 ::
  MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_8 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_problem_200 = erased
-- VerifiedCompilation.UCaseReduce.Inductive.CaseReduce'
d_CaseReduce''_202 a0 a1 a2 = ()
data T_CaseReduce''_202
  = C_casereduce''_218 MAlonzo.Code.Untyped.T__'8866'_14
                       [MAlonzo.Code.Untyped.T__'8866'_14]
                       [MAlonzo.Code.Untyped.T__'8866'_14] Integer
                       MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_8
                       MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
-- VerifiedCompilation.UCaseReduce.Inductive.CaseReduce''
d_CaseReduce''''_222 a0 a1 a2 = ()
data T_CaseReduce''''_222
  = C_casereduce''''_238 MAlonzo.Code.Untyped.T__'8866'_14
                         [MAlonzo.Code.Untyped.T__'8866'_14] Integer
                         MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_8
                         MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_8
-- VerifiedCompilation.UCaseReduce.Inductive.cr''
d_cr''''_242 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14
d_cr''''_242 v0 v1
  = case coe v1 of
      MAlonzo.Code.Untyped.C_'96'_18 v2 -> coe v1
      MAlonzo.Code.Untyped.C_ƛ_20 v2
        -> coe
             MAlonzo.Code.Untyped.C_ƛ_20
             (coe
                d_cr''''_242 (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v2))
      MAlonzo.Code.Untyped.C__'183'__22 v2 v3
        -> coe
             MAlonzo.Code.Untyped.C__'183'__22
             (coe d_cr''''_242 (coe v0) (coe v2))
             (coe d_cr''''_242 (coe v0) (coe v3))
      MAlonzo.Code.Untyped.C_force_24 v2
        -> coe
             MAlonzo.Code.Untyped.C_force_24
             (coe d_cr''''_242 (coe v0) (coe v2))
      MAlonzo.Code.Untyped.C_delay_26 v2
        -> coe
             MAlonzo.Code.Untyped.C_delay_26
             (coe d_cr''''_242 (coe v0) (coe v2))
      MAlonzo.Code.Untyped.C_con_28 v2 -> coe v1
      MAlonzo.Code.Untyped.C_constr_34 v2 v3
        -> coe
             MAlonzo.Code.Untyped.C_constr_34 (coe v2)
             (coe d_cr'''''42'_246 (coe v0) (coe v3))
      MAlonzo.Code.Untyped.C_case_40 v2 v3
        -> let v4 = d_cr''''_242 (coe v0) (coe v2) in
           coe
             (let v5
                    = \ v5 ->
                        coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158 in
              coe
                (let v6
                       = \ v6 ->
                           coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158 in
                 coe
                   (case coe v4 of
                      MAlonzo.Code.Untyped.C_'96'_18 v7
                        -> coe
                             MAlonzo.Code.Untyped.C_case_40 (coe v4)
                             (coe d_cr'''''42'_246 (coe v0) (coe v3))
                      MAlonzo.Code.Untyped.C_ƛ_20 v7
                        -> coe
                             MAlonzo.Code.Untyped.C_case_40 (coe v4)
                             (coe d_cr'''''42'_246 (coe v0) (coe v3))
                      MAlonzo.Code.Untyped.C__'183'__22 v7 v8
                        -> coe
                             MAlonzo.Code.Untyped.C_case_40 (coe v4)
                             (coe d_cr'''''42'_246 (coe v0) (coe v3))
                      MAlonzo.Code.Untyped.C_force_24 v7
                        -> coe
                             MAlonzo.Code.Untyped.C_case_40 (coe v4)
                             (coe d_cr'''''42'_246 (coe v0) (coe v3))
                      MAlonzo.Code.Untyped.C_delay_26 v7
                        -> coe
                             MAlonzo.Code.Untyped.C_case_40 (coe v4)
                             (coe d_cr'''''42'_246 (coe v0) (coe v3))
                      MAlonzo.Code.Untyped.C_con_28 v7
                        -> coe
                             MAlonzo.Code.Untyped.C_case_40 (coe v4)
                             (coe d_cr'''''42'_246 (coe v0) (coe v3))
                      MAlonzo.Code.Untyped.C_constr_34 v7 v8
                        -> let v9
                                 = coe
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                                     (coe v5 v7) (coe v6 v8) in
                           coe
                             (case coe v9 of
                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                  -> if coe v10
                                       then case coe v11 of
                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v12
                                                -> case coe v12 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                       -> coe
                                                            seq (coe v13)
                                                            (coe
                                                               seq (coe v14)
                                                               (let v15
                                                                      = coe
                                                                          MAlonzo.Code.Untyped.CEK.du_lookup'63'_996
                                                                          (coe v7) (coe v3) in
                                                                coe
                                                                  (case coe v15 of
                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                                       -> coe
                                                                            d_cr''''_242 (coe v0)
                                                                            (coe
                                                                               MAlonzo.Code.Untyped.Reduction.du_iterApp_242
                                                                               (coe v16) (coe v8))
                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                       -> coe
                                                                            MAlonzo.Code.Untyped.C_case_40
                                                                            (coe v4)
                                                                            (coe
                                                                               d_cr'''''42'_246
                                                                               (coe v0) (coe v3))
                                                                     _ -> MAlonzo.RTE.mazUnreachableError)))
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       else (let v12
                                                   = seq
                                                       (coe v11)
                                                       (coe
                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                          (coe v10)
                                                          (coe
                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                             coe
                                               (case coe v12 of
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                                    -> if coe v13
                                                         then case coe v14 of
                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v15
                                                                  -> case coe v15 of
                                                                       MAlonzo.Code.VerifiedCompilation.UntypedViews.C_constr'33'_954 v18 v19
                                                                         -> coe
                                                                              seq (coe v18)
                                                                              (coe
                                                                                 seq (coe v19)
                                                                                 (let v20
                                                                                        = coe
                                                                                            MAlonzo.Code.Untyped.CEK.du_lookup'63'_996
                                                                                            (coe v7)
                                                                                            (coe
                                                                                               v3) in
                                                                                  coe
                                                                                    (case coe v20 of
                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v21
                                                                                         -> coe
                                                                                              d_cr''''_242
                                                                                              (coe
                                                                                                 v0)
                                                                                              (coe
                                                                                                 MAlonzo.Code.Untyped.Reduction.du_iterApp_242
                                                                                                 (coe
                                                                                                    v21)
                                                                                                 (coe
                                                                                                    v8))
                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                         -> coe
                                                                                              MAlonzo.Code.Untyped.C_case_40
                                                                                              (coe
                                                                                                 v4)
                                                                                              (coe
                                                                                                 d_cr'''''42'_246
                                                                                                 (coe
                                                                                                    v0)
                                                                                                 (coe
                                                                                                    v3))
                                                                                       _ -> MAlonzo.RTE.mazUnreachableError)))
                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         else coe
                                                                seq (coe v14)
                                                                (coe
                                                                   MAlonzo.Code.Untyped.C_case_40
                                                                   (coe v4)
                                                                   (coe
                                                                      d_cr'''''42'_246 (coe v0)
                                                                      (coe v3)))
                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                                _ -> MAlonzo.RTE.mazUnreachableError)
                      MAlonzo.Code.Untyped.C_case_40 v7 v8
                        -> coe
                             MAlonzo.Code.Untyped.C_case_40 (coe v4)
                             (coe d_cr'''''42'_246 (coe v0) (coe v3))
                      MAlonzo.Code.Untyped.C_builtin_44 v7
                        -> coe
                             MAlonzo.Code.Untyped.C_case_40 (coe v4)
                             (coe d_cr'''''42'_246 (coe v0) (coe v3))
                      MAlonzo.Code.Untyped.C_error_46
                        -> coe
                             MAlonzo.Code.Untyped.C_case_40 (coe v4)
                             (coe d_cr'''''42'_246 (coe v0) (coe v3))
                      _ -> MAlonzo.RTE.mazUnreachableError)))
      MAlonzo.Code.Untyped.C_builtin_44 v2 -> coe v1
      MAlonzo.Code.Untyped.C_error_46 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.UCaseReduce.Inductive.cr''*
d_cr'''''42'_246 ::
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14]
d_cr'''''42'_246 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe d_cr''''_242 (coe v0) (coe v2))
             (coe d_cr'''''42'_246 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.UCaseReduce.Inductive.cr-CR''
d_cr'45'CR''''_348
  = error
      "MAlonzo Runtime Error: postulate evaluated: VerifiedCompilation.UCaseReduce.Inductive.cr-CR''"
