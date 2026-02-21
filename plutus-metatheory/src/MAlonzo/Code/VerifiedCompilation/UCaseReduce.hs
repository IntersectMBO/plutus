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
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects
import qualified MAlonzo.Code.Untyped
import qualified MAlonzo.Code.Untyped.CEK
import qualified MAlonzo.Code.Untyped.Equality
import qualified MAlonzo.Code.Untyped.Reduction
import qualified MAlonzo.Code.VerifiedCompilation.Certificate
import qualified MAlonzo.Code.VerifiedCompilation.UntypedTranslation
import qualified MAlonzo.Code.VerifiedCompilation.UntypedViews

-- VerifiedCompilation.UCaseReduce.CaseReduce
d_CaseReduce_4 a0 a1 a2 = ()
newtype T_CaseReduce_4
  = C_casereduce_16 MAlonzo.Code.Untyped.T__'8866'_14
-- VerifiedCompilation.UCaseReduce.isCaseReduce?
d_isCaseReduce'63'_24 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_86
d_isCaseReduce'63'_24 v0
  = coe
      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.du_translation'63'_164
      (coe v0)
      (coe MAlonzo.Code.VerifiedCompilation.Certificate.C_caseReduceT_14)
      (coe d_isCR'63'_40)
-- VerifiedCompilation.UCaseReduce.justEq
d_justEq_32 ::
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_justEq_32 = erased
-- VerifiedCompilation.UCaseReduce.isCR?
d_isCR'63'_40 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_86
d_isCR'63'_40 v0 v1 v2
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
                                                                              = MAlonzo.Code.Untyped.Equality.d_decEq'45''8866'_52
                                                                                  (coe v0) (coe v2)
                                                                                  (coe
                                                                                     MAlonzo.Code.Untyped.Reduction.du_iterApp_242
                                                                                     (coe v19)
                                                                                     (coe v17)) in
                                                                        coe
                                                                          (case coe v20 of
                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                                                               -> if coe v21
                                                                                    then coe
                                                                                           seq
                                                                                           (coe v22)
                                                                                           (coe
                                                                                              MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_92
                                                                                              (coe
                                                                                                 C_casereduce_16
                                                                                                 v19))
                                                                                    else coe
                                                                                           seq
                                                                                           (coe v22)
                                                                                           (coe
                                                                                              MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_100
                                                                                              (coe
                                                                                                 MAlonzo.Code.VerifiedCompilation.Certificate.C_caseReduceT_14)
                                                                                              v1 v2)
                                                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                     -> coe
                                                                          MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_100
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
                          MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_100
                          (coe MAlonzo.Code.VerifiedCompilation.Certificate.C_caseReduceT_14)
                          v1 v2)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.UCaseReduce.UCaseReduce
d_UCaseReduce_138 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> ()
d_UCaseReduce_138 = erased
-- VerifiedCompilation.UCaseReduce.ast₁
d_ast'8321'_140 :: MAlonzo.Code.Untyped.T__'8866'_14
d_ast'8321'_140
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
d_ast'8321'''_142 :: MAlonzo.Code.Untyped.T__'8866'_14
d_ast'8321'''_142
  = coe
      MAlonzo.Code.Untyped.C__'183'__22
      (coe
         MAlonzo.Code.Untyped.C_'96'_18
         (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
      (coe
         MAlonzo.Code.Untyped.du_con'45'integer_330 (coe (99 :: Integer)))
-- VerifiedCompilation.UCaseReduce.ast
d_ast_146 :: MAlonzo.Code.Untyped.T__'8866'_14
d_ast_146
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
d_ast''_148 :: MAlonzo.Code.Untyped.T__'8866'_14
d_ast''_148
  = coe
      MAlonzo.Code.Untyped.C__'183'__22
      (coe
         MAlonzo.Code.Untyped.du_con'45'integer_330 (coe (42 :: Integer)))
      (coe
         MAlonzo.Code.Untyped.du_con'45'integer_330 (coe (99 :: Integer)))
-- VerifiedCompilation.UCaseReduce.ex1
d_ex1_150 :: MAlonzo.Code.Untyped.T__'8866'_14
d_ex1_150
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
d_ex2_152 :: MAlonzo.Code.Untyped.T__'8866'_14
d_ex2_152
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
