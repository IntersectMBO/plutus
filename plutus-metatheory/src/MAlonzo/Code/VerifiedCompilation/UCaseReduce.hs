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

module MAlonzo.Code.VerifiedCompilation.UCaseReduce where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Builtin
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects
import qualified MAlonzo.Code.Untyped
import qualified MAlonzo.Code.Untyped.CEK
import qualified MAlonzo.Code.Untyped.Reduction
import qualified MAlonzo.Code.VerifiedCompilation.Certificate
import qualified MAlonzo.Code.VerifiedCompilation.UntypedTranslation
import qualified MAlonzo.Code.VerifiedCompilation.UntypedViews

-- VerifiedCompilation.UCaseReduce.CaseReduce
d_CaseReduce_4 a0 a1 a2 = ()
data T_CaseReduce_4
  = C_casereduce_18 MAlonzo.Code.Untyped.T__'8866'_14
                    MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_12
-- VerifiedCompilation.UCaseReduce.isCaseReduce?
d_isCaseReduce'63'_26 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_28
d_isCaseReduce'63'_26 v0
  = coe
      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.du_translation'63'_164
      (coe v0)
      (coe MAlonzo.Code.VerifiedCompilation.Certificate.C_caseReduceT_14)
      (coe d_isCR'63'_42)
-- VerifiedCompilation.UCaseReduce.justEq
d_justEq_34 ::
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_justEq_34 = erased
-- VerifiedCompilation.UCaseReduce.isCR?
d_isCR'63'_42 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_28
d_isCR'63'_42 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isCase'63'_598
              (coe v0)
              (coe
                 (\ v3 ->
                    coe
                      MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isConstr'63'_496
                      (coe v3)
                      (\ v4 v5 ->
                         coe
                           MAlonzo.Code.VerifiedCompilation.UntypedViews.du_allTerms'63'_798)))
              (\ v3 v4 ->
                 coe
                   MAlonzo.Code.VerifiedCompilation.UntypedViews.du_allTerms'63'_798)
              (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then case coe v5 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v6
                         -> case coe v6 of
                              MAlonzo.Code.VerifiedCompilation.UntypedViews.C_iscase_586 v9 v10
                                -> case coe v1 of
                                     MAlonzo.Code.Untyped.C_case_40 v11 v12
                                       -> case coe v9 of
                                            MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isconstr_488 v15
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
                                                                                  d_isCaseReduce'63'_26
                                                                                  v0
                                                                                  (coe
                                                                                     MAlonzo.Code.Untyped.Reduction.du_iterApp_242
                                                                                     (coe v19)
                                                                                     (coe v17))
                                                                                  v2 in
                                                                        coe
                                                                          (case coe v20 of
                                                                             MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_34 v21
                                                                               -> coe
                                                                                    MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_34
                                                                                    (coe
                                                                                       C_casereduce_18
                                                                                       v19 v21)
                                                                             MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_42 v24 v25 v26
                                                                               -> coe
                                                                                    MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_42
                                                                                    v24 v25 v26
                                                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                     -> coe
                                                                          MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_42
                                                                          (coe
                                                                             MAlonzo.Code.VerifiedCompilation.Certificate.C_caseReduceT_14)
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
                          MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_42
                          (coe MAlonzo.Code.VerifiedCompilation.Certificate.C_caseReduceT_14)
                          v1 v2)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.UCaseReduce..extendedlambda0
d_'46'extendedlambda0_58 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isCase_574 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  T_CaseReduce_4 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda0_58 = erased
-- VerifiedCompilation.UCaseReduce..extendedlambda1
d_'46'extendedlambda1_86 ::
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  T_CaseReduce_4 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda1_86 = erased
-- VerifiedCompilation.UCaseReduce..extendedlambda2
d_'46'extendedlambda2_90 ::
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda2_90 = erased
-- VerifiedCompilation.UCaseReduce..extendedlambda3
d_'46'extendedlambda3_142 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4 ->
  AgdaAny ->
  AgdaAny ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_CaseReduce_4 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda3_142 = erased
-- VerifiedCompilation.UCaseReduce.UCaseReduce
d_UCaseReduce_150 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> ()
d_UCaseReduce_150 = erased
-- VerifiedCompilation.UCaseReduce.ast₁
d_ast'8321'_152 :: MAlonzo.Code.Untyped.T__'8866'_14
d_ast'8321'_152
  = coe
      MAlonzo.Code.Untyped.C_case_40
      (coe
         MAlonzo.Code.Untyped.C_constr_34 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Data.List.Base.du_'91'_'93'_286
            (coe
               MAlonzo.Code.Untyped.du_con'45'integer_330 (coe (99 :: Integer)))))
      (coe
         MAlonzo.Code.Data.List.Base.du_'91'_'93'_286
         (coe
            MAlonzo.Code.Untyped.C_'96'_18
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- VerifiedCompilation.UCaseReduce.ast₁'
d_ast'8321'''_154 :: MAlonzo.Code.Untyped.T__'8866'_14
d_ast'8321'''_154
  = coe
      MAlonzo.Code.Untyped.C__'183'__22
      (coe
         MAlonzo.Code.Untyped.C_'96'_18
         (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
      (coe
         MAlonzo.Code.Untyped.du_con'45'integer_330 (coe (99 :: Integer)))
-- VerifiedCompilation.UCaseReduce.ast
d_ast_158 :: MAlonzo.Code.Untyped.T__'8866'_14
d_ast_158
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
                           MAlonzo.Code.Data.List.Base.du_'91'_'93'_286
                           (coe
                              MAlonzo.Code.Untyped.du_con'45'integer_330 (coe (99 :: Integer)))))
                     (coe
                        MAlonzo.Code.Data.List.Base.du_'91'_'93'_286
                        (coe
                           MAlonzo.Code.Untyped.C_'96'_18
                           (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
-- VerifiedCompilation.UCaseReduce.ast'
d_ast''_160 :: MAlonzo.Code.Untyped.T__'8866'_14
d_ast''_160
  = coe
      MAlonzo.Code.Untyped.C__'183'__22
      (coe
         MAlonzo.Code.Untyped.du_con'45'integer_330 (coe (42 :: Integer)))
      (coe
         MAlonzo.Code.Untyped.du_con'45'integer_330 (coe (99 :: Integer)))
-- VerifiedCompilation.UCaseReduce.ex1
d_ex1_162 :: MAlonzo.Code.Untyped.T__'8866'_14
d_ex1_162
  = coe
      MAlonzo.Code.Untyped.C__'183'__22
      (coe
         MAlonzo.Code.Untyped.C__'183'__22
         (coe
            MAlonzo.Code.Untyped.C_ƛ_20
            (coe
               MAlonzo.Code.Untyped.C_ƛ_20
               (coe
                  MAlonzo.Code.Untyped.C__'183'__22
                  (coe
                     MAlonzo.Code.Untyped.C__'183'__22
                     (coe
                        MAlonzo.Code.Untyped.C_builtin_44
                        (coe MAlonzo.Code.Builtin.C_subtractInteger_6))
                     (coe
                        MAlonzo.Code.Untyped.C_'96'_18
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                  (coe
                     MAlonzo.Code.Untyped.C_'96'_18
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
         (coe
            MAlonzo.Code.Untyped.du_con'45'integer_330 (coe (2 :: Integer))))
      (coe
         MAlonzo.Code.Untyped.du_con'45'integer_330 (coe (3 :: Integer)))
-- VerifiedCompilation.UCaseReduce.ex2
d_ex2_164 :: MAlonzo.Code.Untyped.T__'8866'_14
d_ex2_164
  = coe
      MAlonzo.Code.Untyped.C__'183'__22
      (coe
         MAlonzo.Code.Untyped.C__'183'__22
         (coe
            MAlonzo.Code.Untyped.C_ƛ_20
            (coe
               MAlonzo.Code.Untyped.C_ƛ_20
               (coe
                  MAlonzo.Code.Untyped.C__'183'__22
                  (coe
                     MAlonzo.Code.Untyped.C__'183'__22
                     (coe
                        MAlonzo.Code.Untyped.C_builtin_44
                        (coe MAlonzo.Code.Builtin.C_subtractInteger_6))
                     (coe
                        MAlonzo.Code.Untyped.C_'96'_18
                        (coe
                           MAlonzo.Code.Data.Fin.Base.C_suc_16
                           (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                  (coe
                     MAlonzo.Code.Untyped.C_'96'_18
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
         (coe
            MAlonzo.Code.Untyped.du_con'45'integer_330 (coe (3 :: Integer))))
      (coe
         MAlonzo.Code.Untyped.du_con'45'integer_330 (coe (2 :: Integer)))
