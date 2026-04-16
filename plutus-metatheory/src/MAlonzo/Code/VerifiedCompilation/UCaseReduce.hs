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
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Builtin.Constant.AtomicType
import qualified MAlonzo.Code.Builtin.Signature
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Bool.Properties
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.RawU
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects
import qualified MAlonzo.Code.Untyped
import qualified MAlonzo.Code.Untyped.CEK
import qualified MAlonzo.Code.Untyped.Equality
import qualified MAlonzo.Code.Untyped.Reduction
import qualified MAlonzo.Code.Untyped.Relation
import qualified MAlonzo.Code.Untyped.Relation.Composable
import qualified MAlonzo.Code.Untyped.Relation.Properties
import qualified MAlonzo.Code.Untyped.Transform
import qualified MAlonzo.Code.Utils
import qualified MAlonzo.Code.VerifiedCompilation.Certificate
import qualified MAlonzo.Code.VerifiedCompilation.Trace
import qualified MAlonzo.Code.VerifiedCompilation.UntypedViews

-- VerifiedCompilation.UCaseReduce.Rules.CaseConstr
d_CaseConstr_24 a0 a1 a2 a3 = ()
newtype T_CaseConstr_24
  = C_case'45'constr_38 MAlonzo.Code.Untyped.T__'8866'_14
-- VerifiedCompilation.UCaseReduce.Rules.CaseUnit
d_CaseUnit_42 a0 a1 a2 a3 = ()
data T_CaseUnit_42 = C_case'45'unit_50
-- VerifiedCompilation.UCaseReduce.Rules.CaseFalse₁
d_CaseFalse'8321'_54 a0 a1 a2 a3 = ()
data T_CaseFalse'8321'_54 = C_case'45'false'8321'_62
-- VerifiedCompilation.UCaseReduce.Rules.CaseBool
d_CaseBool_66 a0 a1 a2 a3 = ()
data T_CaseBool_66 = C_case'45'bool_78
-- VerifiedCompilation.UCaseReduce.Rules.CaseInteger
d_CaseInteger_82 a0 a1 a2 a3 = ()
data T_CaseInteger_82 = C_case'45'integer_94
-- VerifiedCompilation.UCaseReduce.Rules.CaseCons₁
d_CaseCons'8321'_98 a0 a1 a2 a3 = ()
data T_CaseCons'8321'_98 = C_case'45'cons'8321'_112
-- VerifiedCompilation.UCaseReduce.Rules.CaseCons₂
d_CaseCons'8322'_116 a0 a1 a2 a3 = ()
data T_CaseCons'8322'_116 = C_case'45'cons'8322'_132
-- VerifiedCompilation.UCaseReduce.Rules.CaseNil
d_CaseNil_136 a0 a1 a2 a3 = ()
data T_CaseNil_136 = C_case'45'nil_148
-- VerifiedCompilation.UCaseReduce.Rules.CasePair
d_CasePair_152 a0 a1 a2 a3 = ()
data T_CasePair_152 = C_case'45'pair_168
-- VerifiedCompilation.UCaseReduce.Reduction
d_Reduction_170 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> ()
d_Reduction_170 = erased
-- VerifiedCompilation.UCaseReduce.CaseReduce
d_CaseReduce_172 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> ()
d_CaseReduce_172 = erased
-- VerifiedCompilation.UCaseReduce.cr-refl'
d_cr'45'refl''_200 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Untyped.Relation.T_Mu_36
d_cr'45'refl''_200 ~v0 ~v1 ~v2 ~v3 = du_cr'45'refl''_200
du_cr'45'refl''_200 :: MAlonzo.Code.Untyped.Relation.T_Mu_36
du_cr'45'refl''_200
  = coe
      MAlonzo.Code.Untyped.Relation.C_fix_46
      (coe
         MAlonzo.Code.Untyped.Relation.C_inr_32
         (coe
            MAlonzo.Code.Untyped.Relation.C_inr_32
            (coe
               MAlonzo.Code.Untyped.Relation.C_inr_32
               (coe
                  MAlonzo.Code.Untyped.Relation.C_inr_32
                  (coe MAlonzo.Code.Untyped.Relation.Composable.C_reflF_188)))))
-- VerifiedCompilation.UCaseReduce.cr-refl*
d_cr'45'refl'42'_206
  = error
      "MAlonzo Runtime Error: postulate evaluated: VerifiedCompilation.UCaseReduce.cr-refl*"
-- VerifiedCompilation.UCaseReduce.cr-termcompat
d_cr'45'termcompat_208
  = error
      "MAlonzo Runtime Error: postulate evaluated: VerifiedCompilation.UCaseReduce.cr-termcompat"
-- VerifiedCompilation.UCaseReduce.Test.M
d_M_212 :: MAlonzo.Code.Untyped.T__'8866'_14
d_M_212
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
-- VerifiedCompilation.UCaseReduce.Test.M'
d_M''_214 :: MAlonzo.Code.Untyped.T__'8866'_14
d_M''_214
  = coe
      MAlonzo.Code.Untyped.C_constr_34 (coe (0 :: Integer))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- VerifiedCompilation.UCaseReduce.Test.MM'
d_MM''_216 :: MAlonzo.Code.Untyped.Relation.T_Mu_36
d_MM''_216
  = coe
      MAlonzo.Code.Untyped.Relation.C_fix_46
      (coe
         MAlonzo.Code.Untyped.Relation.C_inl_24
         (coe
            MAlonzo.Code.Untyped.Relation.C_inl_24
            (coe
               C_case'45'constr_38
               (coe
                  MAlonzo.Code.Untyped.C_constr_34 (coe (0 :: Integer))
                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
-- VerifiedCompilation.UCaseReduce.Test.N
d_N_218 :: MAlonzo.Code.Untyped.T__'8866'_14
d_N_218
  = coe
      MAlonzo.Code.Untyped.C_case_40 (coe d_M_212)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Untyped.C_constr_34 (coe (42 :: Integer))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- VerifiedCompilation.UCaseReduce.Test.N'
d_N''_220 :: MAlonzo.Code.Untyped.T__'8866'_14
d_N''_220
  = coe
      MAlonzo.Code.Untyped.C_constr_34 (coe (42 :: Integer))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- VerifiedCompilation.UCaseReduce.red-constr
d_red'45'constr_226 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_red'45'constr_226 ~v0 v1 = du_red'45'constr_226 v1
du_red'45'constr_226 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_red'45'constr_226 v0
  = let v1
          = coe
              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_constr'63'_1618
              (\ v1 ->
                 coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)
              (\ v1 ->
                 coe
                   MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158) in
    coe
      (let v2
             = \ v2 ->
                 coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158 in
       coe
         (case coe v0 of
            MAlonzo.Code.Untyped.C_'96'_18 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_ƛ_20 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C__'183'__22 v3 v4
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_force_24 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_delay_26 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_con_28 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_constr_34 v3 v4
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_case_40 v3 v4
              -> let v5
                       = coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                           (coe v1 v3) (coe v2 v4) in
                 coe
                   (case coe v5 of
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                        -> if coe v6
                             then case coe v7 of
                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v8
                                      -> case coe v8 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                             -> case coe v9 of
                                                  MAlonzo.Code.VerifiedCompilation.UntypedViews.C_constr'33'_954 v13 v14
                                                    -> case coe v3 of
                                                         MAlonzo.Code.Untyped.C_constr_34 v15 v16
                                                           -> coe
                                                                seq (coe v13)
                                                                (coe
                                                                   seq (coe v14)
                                                                   (coe
                                                                      seq (coe v10)
                                                                      (let v17
                                                                             = coe
                                                                                 MAlonzo.Code.Untyped.CEK.du_lookup'63'_996
                                                                                 (coe v15)
                                                                                 (coe v4) in
                                                                       coe
                                                                         (case coe v17 of
                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v18
                                                                              -> coe
                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                      (coe
                                                                                         MAlonzo.Code.Untyped.Reduction.du_iterApp_242
                                                                                         (coe v18)
                                                                                         (coe v16))
                                                                                      (coe
                                                                                         C_case'45'constr_38
                                                                                         v18))
                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                              -> coe v17
                                                                            _ -> MAlonzo.RTE.mazUnreachableError))))
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             else (let v8
                                         = seq
                                             (coe v7)
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                (coe v6)
                                                (coe
                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                   coe
                                     (case coe v8 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                          -> if coe v9
                                               then case coe v10 of
                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v11
                                                        -> case coe v11 of
                                                             MAlonzo.Code.VerifiedCompilation.UntypedViews.C_case'33'_936 v14 v15
                                                               -> case coe v14 of
                                                                    MAlonzo.Code.VerifiedCompilation.UntypedViews.C_constr'33'_954 v18 v19
                                                                      -> case coe v3 of
                                                                           MAlonzo.Code.Untyped.C_constr_34 v20 v21
                                                                             -> coe
                                                                                  seq (coe v18)
                                                                                  (coe
                                                                                     seq (coe v19)
                                                                                     (coe
                                                                                        seq
                                                                                        (coe v15)
                                                                                        (let v22
                                                                                               = coe
                                                                                                   MAlonzo.Code.Untyped.CEK.du_lookup'63'_996
                                                                                                   (coe
                                                                                                      v20)
                                                                                                   (coe
                                                                                                      v4) in
                                                                                         coe
                                                                                           (case coe
                                                                                                   v22 of
                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v23
                                                                                                -> coe
                                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Untyped.Reduction.du_iterApp_242
                                                                                                           (coe
                                                                                                              v23)
                                                                                                           (coe
                                                                                                              v21))
                                                                                                        (coe
                                                                                                           C_case'45'constr_38
                                                                                                           v23))
                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                -> coe
                                                                                                     v22
                                                                                              _ -> MAlonzo.RTE.mazUnreachableError))))
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               else coe
                                                      seq (coe v10)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                      _ -> MAlonzo.RTE.mazUnreachableError)
            MAlonzo.Code.Untyped.C_builtin_44 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_error_46
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            _ -> MAlonzo.RTE.mazUnreachableError))
-- VerifiedCompilation.UCaseReduce.red-unit
d_red'45'unit_268 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_red'45'unit_268 ~v0 v1 = du_red'45'unit_268 v1
du_red'45'unit_268 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_red'45'unit_268 v0
  = let v1
          = coe
              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_con'63'_1732
              (coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du_tmCon'63'_1918
                 (coe
                    MAlonzo.Code.Builtin.Signature.C_atomic_12
                    (coe MAlonzo.Code.Builtin.Constant.AtomicType.C_aUnit_14))
                 (\ v1 ->
                    coe
                      MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du__'8759''63'__2188
                 (\ v2 ->
                    coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)
                 (coe
                    MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'91''93''63'_2244) in
       coe
         (case coe v0 of
            MAlonzo.Code.Untyped.C_'96'_18 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_ƛ_20 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C__'183'__22 v3 v4
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_force_24 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_delay_26 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_con_28 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_constr_34 v3 v4
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_case_40 v3 v4
              -> let v5
                       = coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                           (coe v1 v3) (coe v2 v4) in
                 coe
                   (case coe v5 of
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                        -> if coe v6
                             then case coe v7 of
                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v8
                                      -> case coe v8 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                             -> case coe v9 of
                                                  MAlonzo.Code.VerifiedCompilation.UntypedViews.C_con'33'_964 v13
                                                    -> case coe v13 of
                                                         MAlonzo.Code.VerifiedCompilation.UntypedViews.C_tmCon'33'_992 v15
                                                           -> coe
                                                                seq (coe v15)
                                                                (case coe v10 of
                                                                   MAlonzo.Code.VerifiedCompilation.UntypedViews.C__'8759''33'__2180 v18 v19
                                                                     -> case coe v4 of
                                                                          (:) v20 v21
                                                                            -> coe
                                                                                 seq (coe v18)
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                       (coe v20)
                                                                                       (coe
                                                                                          C_case'45'unit_50)))
                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             else (let v8
                                         = seq
                                             (coe v7)
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                (coe v6)
                                                (coe
                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                   coe
                                     (case coe v8 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                          -> if coe v9
                                               then case coe v10 of
                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v11
                                                        -> case coe v11 of
                                                             MAlonzo.Code.VerifiedCompilation.UntypedViews.C_case'33'_936 v14 v15
                                                               -> case coe v14 of
                                                                    MAlonzo.Code.VerifiedCompilation.UntypedViews.C_con'33'_964 v18
                                                                      -> case coe v18 of
                                                                           MAlonzo.Code.VerifiedCompilation.UntypedViews.C_tmCon'33'_992 v20
                                                                             -> coe
                                                                                  seq (coe v20)
                                                                                  (case coe v15 of
                                                                                     MAlonzo.Code.VerifiedCompilation.UntypedViews.C__'8759''33'__2180 v23 v24
                                                                                       -> case coe
                                                                                                 v4 of
                                                                                            (:) v25 v26
                                                                                              -> coe
                                                                                                   seq
                                                                                                   (coe
                                                                                                      v23)
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                         (coe
                                                                                                            v25)
                                                                                                         (coe
                                                                                                            C_case'45'unit_50)))
                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               else coe
                                                      seq (coe v10)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                      _ -> MAlonzo.RTE.mazUnreachableError)
            MAlonzo.Code.Untyped.C_builtin_44 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_error_46
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            _ -> MAlonzo.RTE.mazUnreachableError))
-- VerifiedCompilation.UCaseReduce.red-false₁
d_red'45'false'8321'_284 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_red'45'false'8321'_284 ~v0 v1 = du_red'45'false'8321'_284 v1
du_red'45'false'8321'_284 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_red'45'false'8321'_284 v0
  = let v1
          = coe
              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_con'63'_1732
              (coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du_tmCon'63'_1918
                 (coe
                    MAlonzo.Code.Builtin.Signature.C_atomic_12
                    (coe MAlonzo.Code.Builtin.Constant.AtomicType.C_aBool_16))
                 (coe
                    MAlonzo.Code.Data.Bool.Properties.d__'8799'__3196
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du__'8759''63'__2188
                 (\ v2 ->
                    coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)
                 (coe
                    MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'91''93''63'_2244) in
       coe
         (case coe v0 of
            MAlonzo.Code.Untyped.C_'96'_18 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_ƛ_20 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C__'183'__22 v3 v4
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_force_24 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_delay_26 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_con_28 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_constr_34 v3 v4
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_case_40 v3 v4
              -> let v5
                       = coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                           (coe v1 v3) (coe v2 v4) in
                 coe
                   (case coe v5 of
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                        -> if coe v6
                             then case coe v7 of
                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v8
                                      -> case coe v8 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                             -> case coe v9 of
                                                  MAlonzo.Code.VerifiedCompilation.UntypedViews.C_con'33'_964 v13
                                                    -> coe
                                                         seq (coe v13)
                                                         (case coe v10 of
                                                            MAlonzo.Code.VerifiedCompilation.UntypedViews.C__'8759''33'__2180 v16 v17
                                                              -> case coe v4 of
                                                                   (:) v18 v19
                                                                     -> coe
                                                                          seq (coe v16)
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                (coe v18)
                                                                                (coe
                                                                                   C_case'45'false'8321'_62)))
                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             else (let v8
                                         = seq
                                             (coe v7)
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                (coe v6)
                                                (coe
                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                   coe
                                     (case coe v8 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                          -> if coe v9
                                               then case coe v10 of
                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v11
                                                        -> case coe v11 of
                                                             MAlonzo.Code.VerifiedCompilation.UntypedViews.C_case'33'_936 v14 v15
                                                               -> case coe v14 of
                                                                    MAlonzo.Code.VerifiedCompilation.UntypedViews.C_con'33'_964 v18
                                                                      -> coe
                                                                           seq (coe v18)
                                                                           (case coe v15 of
                                                                              MAlonzo.Code.VerifiedCompilation.UntypedViews.C__'8759''33'__2180 v21 v22
                                                                                -> case coe v4 of
                                                                                     (:) v23 v24
                                                                                       -> coe
                                                                                            seq
                                                                                            (coe
                                                                                               v21)
                                                                                            (coe
                                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                               (coe
                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                  (coe
                                                                                                     v23)
                                                                                                  (coe
                                                                                                     C_case'45'false'8321'_62)))
                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               else coe
                                                      seq (coe v10)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                      _ -> MAlonzo.RTE.mazUnreachableError)
            MAlonzo.Code.Untyped.C_builtin_44 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_error_46
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            _ -> MAlonzo.RTE.mazUnreachableError))
-- VerifiedCompilation.UCaseReduce.red-bool
d_red'45'bool_298 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_red'45'bool_298 ~v0 v1 = du_red'45'bool_298 v1
du_red'45'bool_298 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_red'45'bool_298 v0
  = let v1
          = coe
              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_con'63'_1732
              (coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du_tmCon'63'_1918
                 (coe
                    MAlonzo.Code.Builtin.Signature.C_atomic_12
                    (coe MAlonzo.Code.Builtin.Constant.AtomicType.C_aBool_16))
                 (\ v1 ->
                    coe
                      MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du__'8759''63'__2188
                 (\ v2 ->
                    coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)
                 (coe
                    MAlonzo.Code.VerifiedCompilation.UntypedViews.du__'8759''63'__2188
                    (\ v2 ->
                       coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)
                    (coe
                       MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'91''93''63'_2244)) in
       coe
         (case coe v0 of
            MAlonzo.Code.Untyped.C_'96'_18 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_ƛ_20 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C__'183'__22 v3 v4
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_force_24 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_delay_26 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_con_28 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_constr_34 v3 v4
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_case_40 v3 v4
              -> let v5
                       = coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                           (coe v1 v3) (coe v2 v4) in
                 coe
                   (case coe v5 of
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                        -> if coe v6
                             then case coe v7 of
                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v8
                                      -> case coe v8 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                             -> case coe v9 of
                                                  MAlonzo.Code.VerifiedCompilation.UntypedViews.C_con'33'_964 v13
                                                    -> case coe v3 of
                                                         MAlonzo.Code.Untyped.C_con_28 v14
                                                           -> case coe v13 of
                                                                MAlonzo.Code.VerifiedCompilation.UntypedViews.C_tmCon'33'_992 v16
                                                                  -> case coe v14 of
                                                                       MAlonzo.Code.RawU.C_tmCon_206 v17 v18
                                                                         -> coe
                                                                              seq (coe v16)
                                                                              (case coe v10 of
                                                                                 MAlonzo.Code.VerifiedCompilation.UntypedViews.C__'8759''33'__2180 v21 v22
                                                                                   -> case coe v4 of
                                                                                        (:) v23 v24
                                                                                          -> coe
                                                                                               seq
                                                                                               (coe
                                                                                                  v21)
                                                                                               (case coe
                                                                                                       v22 of
                                                                                                  MAlonzo.Code.VerifiedCompilation.UntypedViews.C__'8759''33'__2180 v27 v28
                                                                                                    -> case coe
                                                                                                              v24 of
                                                                                                         (:) v29 v30
                                                                                                           -> coe
                                                                                                                seq
                                                                                                                (coe
                                                                                                                   v27)
                                                                                                                (coe
                                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                   (coe
                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                      (coe
                                                                                                                         MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                                                                         (coe
                                                                                                                            v18)
                                                                                                                         (coe
                                                                                                                            v29)
                                                                                                                         (coe
                                                                                                                            v23))
                                                                                                                      (coe
                                                                                                                         C_case'45'bool_78)))
                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             else (let v8
                                         = seq
                                             (coe v7)
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                (coe v6)
                                                (coe
                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                   coe
                                     (case coe v8 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                          -> if coe v9
                                               then case coe v10 of
                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v11
                                                        -> case coe v11 of
                                                             MAlonzo.Code.VerifiedCompilation.UntypedViews.C_case'33'_936 v14 v15
                                                               -> case coe v14 of
                                                                    MAlonzo.Code.VerifiedCompilation.UntypedViews.C_con'33'_964 v18
                                                                      -> case coe v3 of
                                                                           MAlonzo.Code.Untyped.C_con_28 v19
                                                                             -> case coe v18 of
                                                                                  MAlonzo.Code.VerifiedCompilation.UntypedViews.C_tmCon'33'_992 v21
                                                                                    -> case coe
                                                                                              v19 of
                                                                                         MAlonzo.Code.RawU.C_tmCon_206 v22 v23
                                                                                           -> coe
                                                                                                seq
                                                                                                (coe
                                                                                                   v21)
                                                                                                (case coe
                                                                                                        v15 of
                                                                                                   MAlonzo.Code.VerifiedCompilation.UntypedViews.C__'8759''33'__2180 v26 v27
                                                                                                     -> case coe
                                                                                                               v4 of
                                                                                                          (:) v28 v29
                                                                                                            -> coe
                                                                                                                 seq
                                                                                                                 (coe
                                                                                                                    v26)
                                                                                                                 (case coe
                                                                                                                         v27 of
                                                                                                                    MAlonzo.Code.VerifiedCompilation.UntypedViews.C__'8759''33'__2180 v32 v33
                                                                                                                      -> case coe
                                                                                                                                v29 of
                                                                                                                           (:) v34 v35
                                                                                                                             -> coe
                                                                                                                                  seq
                                                                                                                                  (coe
                                                                                                                                     v32)
                                                                                                                                  (coe
                                                                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                     (coe
                                                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                        (coe
                                                                                                                                           MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                                                                                           (coe
                                                                                                                                              v23)
                                                                                                                                           (coe
                                                                                                                                              v34)
                                                                                                                                           (coe
                                                                                                                                              v28))
                                                                                                                                        (coe
                                                                                                                                           C_case'45'bool_78)))
                                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               else coe
                                                      seq (coe v10)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                      _ -> MAlonzo.RTE.mazUnreachableError)
            MAlonzo.Code.Untyped.C_builtin_44 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_error_46
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            _ -> MAlonzo.RTE.mazUnreachableError))
-- VerifiedCompilation.UCaseReduce.red-integer
d_red'45'integer_316 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_red'45'integer_316 ~v0 v1 = du_red'45'integer_316 v1
du_red'45'integer_316 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_red'45'integer_316 v0
  = let v1
          = coe
              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_con'63'_1732
              (coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du_tmCon'63'_1918
                 (coe
                    MAlonzo.Code.Builtin.Signature.C_atomic_12
                    (coe MAlonzo.Code.Builtin.Constant.AtomicType.C_aInteger_8))
                 (coe
                    MAlonzo.Code.VerifiedCompilation.UntypedViews.d_pos'63'_2342)) in
    coe
      (let v2
             = \ v2 ->
                 coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158 in
       coe
         (case coe v0 of
            MAlonzo.Code.Untyped.C_'96'_18 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_ƛ_20 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C__'183'__22 v3 v4
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_force_24 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_delay_26 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_con_28 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_constr_34 v3 v4
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_case_40 v3 v4
              -> let v5
                       = coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                           (coe v1 v3) (coe v2 v4) in
                 coe
                   (case coe v5 of
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                        -> if coe v6
                             then case coe v7 of
                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v8
                                      -> case coe v8 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                             -> case coe v9 of
                                                  MAlonzo.Code.VerifiedCompilation.UntypedViews.C_con'33'_964 v13
                                                    -> case coe v3 of
                                                         MAlonzo.Code.Untyped.C_con_28 v14
                                                           -> case coe v13 of
                                                                MAlonzo.Code.VerifiedCompilation.UntypedViews.C_tmCon'33'_992 v16
                                                                  -> case coe v14 of
                                                                       MAlonzo.Code.RawU.C_tmCon_206 v17 v18
                                                                         -> coe
                                                                              seq (coe v16)
                                                                              (coe
                                                                                 seq (coe v10)
                                                                                 (let v19
                                                                                        = coe
                                                                                            MAlonzo.Code.Untyped.CEK.du_lookup'63'_996
                                                                                            (coe
                                                                                               v18)
                                                                                            (coe
                                                                                               v4) in
                                                                                  coe
                                                                                    (case coe v19 of
                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v20
                                                                                         -> coe
                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                              (coe
                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                 (coe
                                                                                                    v20)
                                                                                                 (coe
                                                                                                    C_case'45'integer_94))
                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                         -> coe v19
                                                                                       _ -> MAlonzo.RTE.mazUnreachableError)))
                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             else (let v8
                                         = seq
                                             (coe v7)
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                (coe v6)
                                                (coe
                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                   coe
                                     (case coe v8 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                          -> if coe v9
                                               then case coe v10 of
                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v11
                                                        -> case coe v11 of
                                                             MAlonzo.Code.VerifiedCompilation.UntypedViews.C_case'33'_936 v14 v15
                                                               -> case coe v14 of
                                                                    MAlonzo.Code.VerifiedCompilation.UntypedViews.C_con'33'_964 v18
                                                                      -> case coe v3 of
                                                                           MAlonzo.Code.Untyped.C_con_28 v19
                                                                             -> case coe v18 of
                                                                                  MAlonzo.Code.VerifiedCompilation.UntypedViews.C_tmCon'33'_992 v21
                                                                                    -> case coe
                                                                                              v19 of
                                                                                         MAlonzo.Code.RawU.C_tmCon_206 v22 v23
                                                                                           -> coe
                                                                                                seq
                                                                                                (coe
                                                                                                   v21)
                                                                                                (coe
                                                                                                   seq
                                                                                                   (coe
                                                                                                      v15)
                                                                                                   (let v24
                                                                                                          = coe
                                                                                                              MAlonzo.Code.Untyped.CEK.du_lookup'63'_996
                                                                                                              (coe
                                                                                                                 v23)
                                                                                                              (coe
                                                                                                                 v4) in
                                                                                                    coe
                                                                                                      (case coe
                                                                                                              v24 of
                                                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v25
                                                                                                           -> coe
                                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                (coe
                                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                   (coe
                                                                                                                      v25)
                                                                                                                   (coe
                                                                                                                      C_case'45'integer_94))
                                                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                           -> coe
                                                                                                                v24
                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError)))
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               else coe
                                                      seq (coe v10)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                      _ -> MAlonzo.RTE.mazUnreachableError)
            MAlonzo.Code.Untyped.C_builtin_44 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_error_46
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            _ -> MAlonzo.RTE.mazUnreachableError))
-- VerifiedCompilation.UCaseReduce.red-cons₁
d_red'45'cons'8321'_352 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_red'45'cons'8321'_352 ~v0 v1 = du_red'45'cons'8321'_352 v1
du_red'45'cons'8321'_352 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_red'45'cons'8321'_352 v0
  = let v1
          = coe
              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_con'63'_1732
              (coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du_tmCon'45'list'63'_2010
                 (coe
                    (\ v1 ->
                       coe
                         MAlonzo.Code.VerifiedCompilation.UntypedViews.du_cons'63'_2272
                         (\ v2 ->
                            coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)
                         (\ v2 ->
                            coe
                              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)))) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du__'8759''63'__2188
                 (\ v2 ->
                    coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)
                 (coe
                    MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'91''93''63'_2244) in
       coe
         (case coe v0 of
            MAlonzo.Code.Untyped.C_'96'_18 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_ƛ_20 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C__'183'__22 v3 v4
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_force_24 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_delay_26 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_con_28 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_constr_34 v3 v4
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_case_40 v3 v4
              -> let v5
                       = coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                           (coe v1 v3) (coe v2 v4) in
                 coe
                   (case coe v5 of
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                        -> if coe v6
                             then case coe v7 of
                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v8
                                      -> case coe v8 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                             -> case coe v9 of
                                                  MAlonzo.Code.VerifiedCompilation.UntypedViews.C_con'33'_964 v13
                                                    -> case coe v3 of
                                                         MAlonzo.Code.Untyped.C_con_28 v14
                                                           -> case coe v13 of
                                                                MAlonzo.Code.VerifiedCompilation.UntypedViews.C_tmCon'45'list'33'_1006 v17
                                                                  -> case coe v14 of
                                                                       MAlonzo.Code.RawU.C_tmCon_206 v18 v19
                                                                         -> case coe v18 of
                                                                              MAlonzo.Code.Builtin.Signature.C_list_16 v21
                                                                                -> case coe v17 of
                                                                                     MAlonzo.Code.VerifiedCompilation.UntypedViews.C_cons'33'_2264 v24 v25
                                                                                       -> case coe
                                                                                                 v19 of
                                                                                            MAlonzo.Code.Utils.C__'8759'__460 v26 v27
                                                                                              -> coe
                                                                                                   seq
                                                                                                   (coe
                                                                                                      v24)
                                                                                                   (coe
                                                                                                      seq
                                                                                                      (coe
                                                                                                         v25)
                                                                                                      (case coe
                                                                                                              v10 of
                                                                                                         MAlonzo.Code.VerifiedCompilation.UntypedViews.C__'8759''33'__2180 v30 v31
                                                                                                           -> case coe
                                                                                                                     v4 of
                                                                                                                (:) v32 v33
                                                                                                                  -> coe
                                                                                                                       seq
                                                                                                                       (coe
                                                                                                                          v30)
                                                                                                                       (coe
                                                                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                          (coe
                                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Untyped.C__'183'__22
                                                                                                                                (coe
                                                                                                                                   MAlonzo.Code.Untyped.C__'183'__22
                                                                                                                                   (coe
                                                                                                                                      v32)
                                                                                                                                   (coe
                                                                                                                                      MAlonzo.Code.Untyped.C_con_28
                                                                                                                                      (coe
                                                                                                                                         MAlonzo.Code.RawU.C_tmCon_206
                                                                                                                                         (coe
                                                                                                                                            v21)
                                                                                                                                         (coe
                                                                                                                                            v26))))
                                                                                                                                (coe
                                                                                                                                   MAlonzo.Code.Untyped.C_con_28
                                                                                                                                   (coe
                                                                                                                                      MAlonzo.Code.RawU.C_tmCon_206
                                                                                                                                      (coe
                                                                                                                                         MAlonzo.Code.Builtin.Signature.C_list_16
                                                                                                                                         v21)
                                                                                                                                      (coe
                                                                                                                                         v27))))
                                                                                                                             (coe
                                                                                                                                C_case'45'cons'8321'_112)))
                                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             else (let v8
                                         = seq
                                             (coe v7)
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                (coe v6)
                                                (coe
                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                   coe
                                     (case coe v8 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                          -> if coe v9
                                               then case coe v10 of
                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v11
                                                        -> case coe v11 of
                                                             MAlonzo.Code.VerifiedCompilation.UntypedViews.C_case'33'_936 v14 v15
                                                               -> case coe v14 of
                                                                    MAlonzo.Code.VerifiedCompilation.UntypedViews.C_con'33'_964 v18
                                                                      -> case coe v3 of
                                                                           MAlonzo.Code.Untyped.C_con_28 v19
                                                                             -> case coe v18 of
                                                                                  MAlonzo.Code.VerifiedCompilation.UntypedViews.C_tmCon'45'list'33'_1006 v22
                                                                                    -> case coe
                                                                                              v19 of
                                                                                         MAlonzo.Code.RawU.C_tmCon_206 v23 v24
                                                                                           -> case coe
                                                                                                     v23 of
                                                                                                MAlonzo.Code.Builtin.Signature.C_list_16 v26
                                                                                                  -> case coe
                                                                                                            v22 of
                                                                                                       MAlonzo.Code.VerifiedCompilation.UntypedViews.C_cons'33'_2264 v29 v30
                                                                                                         -> case coe
                                                                                                                   v24 of
                                                                                                              MAlonzo.Code.Utils.C__'8759'__460 v31 v32
                                                                                                                -> coe
                                                                                                                     seq
                                                                                                                     (coe
                                                                                                                        v29)
                                                                                                                     (coe
                                                                                                                        seq
                                                                                                                        (coe
                                                                                                                           v30)
                                                                                                                        (case coe
                                                                                                                                v15 of
                                                                                                                           MAlonzo.Code.VerifiedCompilation.UntypedViews.C__'8759''33'__2180 v35 v36
                                                                                                                             -> case coe
                                                                                                                                       v4 of
                                                                                                                                  (:) v37 v38
                                                                                                                                    -> coe
                                                                                                                                         seq
                                                                                                                                         (coe
                                                                                                                                            v35)
                                                                                                                                         (coe
                                                                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                            (coe
                                                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                               (coe
                                                                                                                                                  MAlonzo.Code.Untyped.C__'183'__22
                                                                                                                                                  (coe
                                                                                                                                                     MAlonzo.Code.Untyped.C__'183'__22
                                                                                                                                                     (coe
                                                                                                                                                        v37)
                                                                                                                                                     (coe
                                                                                                                                                        MAlonzo.Code.Untyped.C_con_28
                                                                                                                                                        (coe
                                                                                                                                                           MAlonzo.Code.RawU.C_tmCon_206
                                                                                                                                                           (coe
                                                                                                                                                              v26)
                                                                                                                                                           (coe
                                                                                                                                                              v31))))
                                                                                                                                                  (coe
                                                                                                                                                     MAlonzo.Code.Untyped.C_con_28
                                                                                                                                                     (coe
                                                                                                                                                        MAlonzo.Code.RawU.C_tmCon_206
                                                                                                                                                        (coe
                                                                                                                                                           MAlonzo.Code.Builtin.Signature.C_list_16
                                                                                                                                                           v26)
                                                                                                                                                        (coe
                                                                                                                                                           v32))))
                                                                                                                                               (coe
                                                                                                                                                  C_case'45'cons'8321'_112)))
                                                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               else coe
                                                      seq (coe v10)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                      _ -> MAlonzo.RTE.mazUnreachableError)
            MAlonzo.Code.Untyped.C_builtin_44 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_error_46
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            _ -> MAlonzo.RTE.mazUnreachableError))
-- VerifiedCompilation.UCaseReduce.red-cons₂
d_red'45'cons'8322'_374 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_red'45'cons'8322'_374 ~v0 v1 = du_red'45'cons'8322'_374 v1
du_red'45'cons'8322'_374 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_red'45'cons'8322'_374 v0
  = let v1
          = coe
              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_con'63'_1732
              (coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du_tmCon'45'list'63'_2010
                 (coe
                    (\ v1 ->
                       coe
                         MAlonzo.Code.VerifiedCompilation.UntypedViews.du_cons'63'_2272
                         (\ v2 ->
                            coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)
                         (\ v2 ->
                            coe
                              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)))) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du__'8759''63'__2188
                 (\ v2 ->
                    coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)
                 (coe
                    MAlonzo.Code.VerifiedCompilation.UntypedViews.du__'8759''63'__2188
                    (\ v2 ->
                       coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)
                    (coe
                       MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'91''93''63'_2244)) in
       coe
         (case coe v0 of
            MAlonzo.Code.Untyped.C_'96'_18 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_ƛ_20 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C__'183'__22 v3 v4
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_force_24 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_delay_26 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_con_28 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_constr_34 v3 v4
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_case_40 v3 v4
              -> let v5
                       = coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                           (coe v1 v3) (coe v2 v4) in
                 coe
                   (case coe v5 of
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                        -> if coe v6
                             then case coe v7 of
                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v8
                                      -> case coe v8 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                             -> case coe v9 of
                                                  MAlonzo.Code.VerifiedCompilation.UntypedViews.C_con'33'_964 v13
                                                    -> case coe v3 of
                                                         MAlonzo.Code.Untyped.C_con_28 v14
                                                           -> case coe v13 of
                                                                MAlonzo.Code.VerifiedCompilation.UntypedViews.C_tmCon'45'list'33'_1006 v17
                                                                  -> case coe v14 of
                                                                       MAlonzo.Code.RawU.C_tmCon_206 v18 v19
                                                                         -> case coe v18 of
                                                                              MAlonzo.Code.Builtin.Signature.C_list_16 v21
                                                                                -> case coe v17 of
                                                                                     MAlonzo.Code.VerifiedCompilation.UntypedViews.C_cons'33'_2264 v24 v25
                                                                                       -> case coe
                                                                                                 v19 of
                                                                                            MAlonzo.Code.Utils.C__'8759'__460 v26 v27
                                                                                              -> coe
                                                                                                   seq
                                                                                                   (coe
                                                                                                      v24)
                                                                                                   (coe
                                                                                                      seq
                                                                                                      (coe
                                                                                                         v25)
                                                                                                      (case coe
                                                                                                              v10 of
                                                                                                         MAlonzo.Code.VerifiedCompilation.UntypedViews.C__'8759''33'__2180 v30 v31
                                                                                                           -> case coe
                                                                                                                     v4 of
                                                                                                                (:) v32 v33
                                                                                                                  -> coe
                                                                                                                       seq
                                                                                                                       (coe
                                                                                                                          v30)
                                                                                                                       (case coe
                                                                                                                               v31 of
                                                                                                                          MAlonzo.Code.VerifiedCompilation.UntypedViews.C__'8759''33'__2180 v36 v37
                                                                                                                            -> coe
                                                                                                                                 seq
                                                                                                                                 (coe
                                                                                                                                    v36)
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                       (coe
                                                                                                                                          MAlonzo.Code.Untyped.C__'183'__22
                                                                                                                                          (coe
                                                                                                                                             MAlonzo.Code.Untyped.C__'183'__22
                                                                                                                                             (coe
                                                                                                                                                v32)
                                                                                                                                             (coe
                                                                                                                                                MAlonzo.Code.Untyped.C_con_28
                                                                                                                                                (coe
                                                                                                                                                   MAlonzo.Code.RawU.C_tmCon_206
                                                                                                                                                   (coe
                                                                                                                                                      v21)
                                                                                                                                                   (coe
                                                                                                                                                      v26))))
                                                                                                                                          (coe
                                                                                                                                             MAlonzo.Code.Untyped.C_con_28
                                                                                                                                             (coe
                                                                                                                                                MAlonzo.Code.RawU.C_tmCon_206
                                                                                                                                                (coe
                                                                                                                                                   MAlonzo.Code.Builtin.Signature.C_list_16
                                                                                                                                                   v21)
                                                                                                                                                (coe
                                                                                                                                                   v27))))
                                                                                                                                       (coe
                                                                                                                                          C_case'45'cons'8322'_132)))
                                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             else (let v8
                                         = seq
                                             (coe v7)
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                (coe v6)
                                                (coe
                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                   coe
                                     (case coe v8 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                          -> if coe v9
                                               then case coe v10 of
                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v11
                                                        -> case coe v11 of
                                                             MAlonzo.Code.VerifiedCompilation.UntypedViews.C_case'33'_936 v14 v15
                                                               -> case coe v14 of
                                                                    MAlonzo.Code.VerifiedCompilation.UntypedViews.C_con'33'_964 v18
                                                                      -> case coe v3 of
                                                                           MAlonzo.Code.Untyped.C_con_28 v19
                                                                             -> case coe v18 of
                                                                                  MAlonzo.Code.VerifiedCompilation.UntypedViews.C_tmCon'45'list'33'_1006 v22
                                                                                    -> case coe
                                                                                              v19 of
                                                                                         MAlonzo.Code.RawU.C_tmCon_206 v23 v24
                                                                                           -> case coe
                                                                                                     v23 of
                                                                                                MAlonzo.Code.Builtin.Signature.C_list_16 v26
                                                                                                  -> case coe
                                                                                                            v22 of
                                                                                                       MAlonzo.Code.VerifiedCompilation.UntypedViews.C_cons'33'_2264 v29 v30
                                                                                                         -> case coe
                                                                                                                   v24 of
                                                                                                              MAlonzo.Code.Utils.C__'8759'__460 v31 v32
                                                                                                                -> coe
                                                                                                                     seq
                                                                                                                     (coe
                                                                                                                        v29)
                                                                                                                     (coe
                                                                                                                        seq
                                                                                                                        (coe
                                                                                                                           v30)
                                                                                                                        (case coe
                                                                                                                                v15 of
                                                                                                                           MAlonzo.Code.VerifiedCompilation.UntypedViews.C__'8759''33'__2180 v35 v36
                                                                                                                             -> case coe
                                                                                                                                       v4 of
                                                                                                                                  (:) v37 v38
                                                                                                                                    -> coe
                                                                                                                                         seq
                                                                                                                                         (coe
                                                                                                                                            v35)
                                                                                                                                         (case coe
                                                                                                                                                 v36 of
                                                                                                                                            MAlonzo.Code.VerifiedCompilation.UntypedViews.C__'8759''33'__2180 v41 v42
                                                                                                                                              -> coe
                                                                                                                                                   seq
                                                                                                                                                   (coe
                                                                                                                                                      v41)
                                                                                                                                                   (coe
                                                                                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                      (coe
                                                                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                         (coe
                                                                                                                                                            MAlonzo.Code.Untyped.C__'183'__22
                                                                                                                                                            (coe
                                                                                                                                                               MAlonzo.Code.Untyped.C__'183'__22
                                                                                                                                                               (coe
                                                                                                                                                                  v37)
                                                                                                                                                               (coe
                                                                                                                                                                  MAlonzo.Code.Untyped.C_con_28
                                                                                                                                                                  (coe
                                                                                                                                                                     MAlonzo.Code.RawU.C_tmCon_206
                                                                                                                                                                     (coe
                                                                                                                                                                        v26)
                                                                                                                                                                     (coe
                                                                                                                                                                        v31))))
                                                                                                                                                            (coe
                                                                                                                                                               MAlonzo.Code.Untyped.C_con_28
                                                                                                                                                               (coe
                                                                                                                                                                  MAlonzo.Code.RawU.C_tmCon_206
                                                                                                                                                                  (coe
                                                                                                                                                                     MAlonzo.Code.Builtin.Signature.C_list_16
                                                                                                                                                                     v26)
                                                                                                                                                                  (coe
                                                                                                                                                                     v32))))
                                                                                                                                                         (coe
                                                                                                                                                            C_case'45'cons'8322'_132)))
                                                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               else coe
                                                      seq (coe v10)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                      _ -> MAlonzo.RTE.mazUnreachableError)
            MAlonzo.Code.Untyped.C_builtin_44 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_error_46
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            _ -> MAlonzo.RTE.mazUnreachableError))
-- VerifiedCompilation.UCaseReduce.red-nil
d_red'45'nil_396 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_red'45'nil_396 ~v0 v1 = du_red'45'nil_396 v1
du_red'45'nil_396 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_red'45'nil_396 v0
  = let v1
          = coe
              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_con'63'_1732
              (coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du_tmCon'45'list'63'_2010
                 (coe
                    (\ v1 ->
                       coe
                         MAlonzo.Code.VerifiedCompilation.UntypedViews.du_nil'63'_2328))) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du__'8759''63'__2188
                 (\ v2 ->
                    coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)
                 (coe
                    MAlonzo.Code.VerifiedCompilation.UntypedViews.du__'8759''63'__2188
                    (\ v2 ->
                       coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)
                    (coe
                       MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'91''93''63'_2244)) in
       coe
         (case coe v0 of
            MAlonzo.Code.Untyped.C_'96'_18 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_ƛ_20 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C__'183'__22 v3 v4
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_force_24 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_delay_26 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_con_28 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_constr_34 v3 v4
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_case_40 v3 v4
              -> let v5
                       = coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                           (coe v1 v3) (coe v2 v4) in
                 coe
                   (case coe v5 of
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                        -> if coe v6
                             then case coe v7 of
                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v8
                                      -> case coe v8 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                             -> case coe v9 of
                                                  MAlonzo.Code.VerifiedCompilation.UntypedViews.C_con'33'_964 v13
                                                    -> coe
                                                         seq (coe v13)
                                                         (case coe v10 of
                                                            MAlonzo.Code.VerifiedCompilation.UntypedViews.C__'8759''33'__2180 v16 v17
                                                              -> case coe v4 of
                                                                   (:) v18 v19
                                                                     -> coe
                                                                          seq (coe v16)
                                                                          (case coe v17 of
                                                                             MAlonzo.Code.VerifiedCompilation.UntypedViews.C__'8759''33'__2180 v22 v23
                                                                               -> case coe v19 of
                                                                                    (:) v24 v25
                                                                                      -> coe
                                                                                           seq
                                                                                           (coe v22)
                                                                                           (coe
                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                              (coe
                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                 (coe
                                                                                                    v24)
                                                                                                 (coe
                                                                                                    C_case'45'nil_148)))
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             else (let v8
                                         = seq
                                             (coe v7)
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                (coe v6)
                                                (coe
                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                   coe
                                     (case coe v8 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                          -> if coe v9
                                               then case coe v10 of
                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v11
                                                        -> case coe v11 of
                                                             MAlonzo.Code.VerifiedCompilation.UntypedViews.C_case'33'_936 v14 v15
                                                               -> case coe v14 of
                                                                    MAlonzo.Code.VerifiedCompilation.UntypedViews.C_con'33'_964 v18
                                                                      -> coe
                                                                           seq (coe v18)
                                                                           (case coe v15 of
                                                                              MAlonzo.Code.VerifiedCompilation.UntypedViews.C__'8759''33'__2180 v21 v22
                                                                                -> case coe v4 of
                                                                                     (:) v23 v24
                                                                                       -> coe
                                                                                            seq
                                                                                            (coe
                                                                                               v21)
                                                                                            (case coe
                                                                                                    v22 of
                                                                                               MAlonzo.Code.VerifiedCompilation.UntypedViews.C__'8759''33'__2180 v27 v28
                                                                                                 -> case coe
                                                                                                           v24 of
                                                                                                      (:) v29 v30
                                                                                                        -> coe
                                                                                                             seq
                                                                                                             (coe
                                                                                                                v27)
                                                                                                             (coe
                                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                (coe
                                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                   (coe
                                                                                                                      v29)
                                                                                                                   (coe
                                                                                                                      C_case'45'nil_148)))
                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               else coe
                                                      seq (coe v10)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                      _ -> MAlonzo.RTE.mazUnreachableError)
            MAlonzo.Code.Untyped.C_builtin_44 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_error_46
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            _ -> MAlonzo.RTE.mazUnreachableError))
-- VerifiedCompilation.UCaseReduce.red-pair
d_red'45'pair_414 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_red'45'pair_414 ~v0 v1 = du_red'45'pair_414 v1
du_red'45'pair_414 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_red'45'pair_414 v0
  = let v1
          = coe
              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_con'63'_1732
              (coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du_tmCon'45'pair'63'_2080
                 (coe
                    (\ v1 v2 v3 ->
                       coe
                         MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158))) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du__'8759''63'__2188
                 (\ v2 ->
                    coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)
                 (coe
                    MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'91''93''63'_2244) in
       coe
         (case coe v0 of
            MAlonzo.Code.Untyped.C_'96'_18 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_ƛ_20 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C__'183'__22 v3 v4
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_force_24 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_delay_26 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_con_28 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_constr_34 v3 v4
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_case_40 v3 v4
              -> let v5
                       = coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                           (coe v1 v3) (coe v2 v4) in
                 coe
                   (case coe v5 of
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                        -> if coe v6
                             then case coe v7 of
                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v8
                                      -> case coe v8 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                             -> case coe v9 of
                                                  MAlonzo.Code.VerifiedCompilation.UntypedViews.C_con'33'_964 v13
                                                    -> case coe v3 of
                                                         MAlonzo.Code.Untyped.C_con_28 v14
                                                           -> case coe v13 of
                                                                MAlonzo.Code.VerifiedCompilation.UntypedViews.C_tmCon'45'pair'33'_1024 v18
                                                                  -> case coe v14 of
                                                                       MAlonzo.Code.RawU.C_tmCon_206 v19 v20
                                                                         -> case coe v19 of
                                                                              MAlonzo.Code.Builtin.Signature.C_pair_24 v22 v23
                                                                                -> case coe v20 of
                                                                                     MAlonzo.Code.Utils.C__'44'__450 v24 v25
                                                                                       -> coe
                                                                                            seq
                                                                                            (coe
                                                                                               v18)
                                                                                            (case coe
                                                                                                    v10 of
                                                                                               MAlonzo.Code.VerifiedCompilation.UntypedViews.C__'8759''33'__2180 v28 v29
                                                                                                 -> case coe
                                                                                                           v4 of
                                                                                                      (:) v30 v31
                                                                                                        -> coe
                                                                                                             seq
                                                                                                             (coe
                                                                                                                v28)
                                                                                                             (coe
                                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                (coe
                                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                   (coe
                                                                                                                      MAlonzo.Code.Untyped.C__'183'__22
                                                                                                                      (coe
                                                                                                                         MAlonzo.Code.Untyped.C__'183'__22
                                                                                                                         (coe
                                                                                                                            v30)
                                                                                                                         (coe
                                                                                                                            MAlonzo.Code.Untyped.C_con_28
                                                                                                                            (coe
                                                                                                                               MAlonzo.Code.RawU.C_tmCon_206
                                                                                                                               (coe
                                                                                                                                  v22)
                                                                                                                               (coe
                                                                                                                                  v24))))
                                                                                                                      (coe
                                                                                                                         MAlonzo.Code.Untyped.C_con_28
                                                                                                                         (coe
                                                                                                                            MAlonzo.Code.RawU.C_tmCon_206
                                                                                                                            (coe
                                                                                                                               v23)
                                                                                                                            (coe
                                                                                                                               v25))))
                                                                                                                   (coe
                                                                                                                      C_case'45'pair_168)))
                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             else (let v8
                                         = seq
                                             (coe v7)
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                (coe v6)
                                                (coe
                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                   coe
                                     (case coe v8 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                          -> if coe v9
                                               then case coe v10 of
                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v11
                                                        -> case coe v11 of
                                                             MAlonzo.Code.VerifiedCompilation.UntypedViews.C_case'33'_936 v14 v15
                                                               -> case coe v14 of
                                                                    MAlonzo.Code.VerifiedCompilation.UntypedViews.C_con'33'_964 v18
                                                                      -> case coe v3 of
                                                                           MAlonzo.Code.Untyped.C_con_28 v19
                                                                             -> case coe v18 of
                                                                                  MAlonzo.Code.VerifiedCompilation.UntypedViews.C_tmCon'45'pair'33'_1024 v23
                                                                                    -> case coe
                                                                                              v19 of
                                                                                         MAlonzo.Code.RawU.C_tmCon_206 v24 v25
                                                                                           -> case coe
                                                                                                     v24 of
                                                                                                MAlonzo.Code.Builtin.Signature.C_pair_24 v27 v28
                                                                                                  -> case coe
                                                                                                            v25 of
                                                                                                       MAlonzo.Code.Utils.C__'44'__450 v29 v30
                                                                                                         -> coe
                                                                                                              seq
                                                                                                              (coe
                                                                                                                 v23)
                                                                                                              (case coe
                                                                                                                      v15 of
                                                                                                                 MAlonzo.Code.VerifiedCompilation.UntypedViews.C__'8759''33'__2180 v33 v34
                                                                                                                   -> case coe
                                                                                                                             v4 of
                                                                                                                        (:) v35 v36
                                                                                                                          -> coe
                                                                                                                               seq
                                                                                                                               (coe
                                                                                                                                  v33)
                                                                                                                               (coe
                                                                                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                  (coe
                                                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                     (coe
                                                                                                                                        MAlonzo.Code.Untyped.C__'183'__22
                                                                                                                                        (coe
                                                                                                                                           MAlonzo.Code.Untyped.C__'183'__22
                                                                                                                                           (coe
                                                                                                                                              v35)
                                                                                                                                           (coe
                                                                                                                                              MAlonzo.Code.Untyped.C_con_28
                                                                                                                                              (coe
                                                                                                                                                 MAlonzo.Code.RawU.C_tmCon_206
                                                                                                                                                 (coe
                                                                                                                                                    v27)
                                                                                                                                                 (coe
                                                                                                                                                    v29))))
                                                                                                                                        (coe
                                                                                                                                           MAlonzo.Code.Untyped.C_con_28
                                                                                                                                           (coe
                                                                                                                                              MAlonzo.Code.RawU.C_tmCon_206
                                                                                                                                              (coe
                                                                                                                                                 v28)
                                                                                                                                              (coe
                                                                                                                                                 v30))))
                                                                                                                                     (coe
                                                                                                                                        C_case'45'pair_168)))
                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               else coe
                                                      seq (coe v10)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                      _ -> MAlonzo.RTE.mazUnreachableError)
            MAlonzo.Code.Untyped.C_builtin_44 v3
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            MAlonzo.Code.Untyped.C_error_46
              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
            _ -> MAlonzo.RTE.mazUnreachableError))
-- VerifiedCompilation.UCaseReduce.reduce
d_reduce_436 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_reduce_436 v0
  = coe
      MAlonzo.Code.Untyped.Relation.du__'60''124''62'__124
      (\ v1 v2 -> coe du_red'45'constr_226 v2)
      (coe
         MAlonzo.Code.Untyped.Relation.du__'60''124''62'__124
         (\ v1 v2 -> coe du_red'45'unit_268 v2)
         (coe
            MAlonzo.Code.Untyped.Relation.du__'60''124''62'__124
            (\ v1 v2 -> coe du_red'45'false'8321'_284 v2)
            (coe
               MAlonzo.Code.Untyped.Relation.du__'60''124''62'__124
               (\ v1 v2 -> coe du_red'45'bool_298 v2)
               (coe
                  MAlonzo.Code.Untyped.Relation.du__'60''124''62'__124
                  (\ v1 v2 -> coe du_red'45'integer_316 v2)
                  (coe
                     MAlonzo.Code.Untyped.Relation.du__'60''124''62'__124
                     (\ v1 v2 -> coe du_red'45'cons'8321'_352 v2)
                     (coe
                        MAlonzo.Code.Untyped.Relation.du__'60''124''62'__124
                        (\ v1 v2 -> coe du_red'45'cons'8322'_374 v2)
                        (coe
                           MAlonzo.Code.Untyped.Relation.du__'60''124''62'__124
                           (\ v1 v2 -> coe du_red'45'nil_396 v2)
                           (\ v1 v2 -> coe du_red'45'pair_414 v2))))))))
      (coe v0)
-- VerifiedCompilation.UCaseReduce.reduceM
d_reduceM_440 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Maybe MAlonzo.Code.Untyped.T__'8866'_14
d_reduceM_440 v0
  = coe
      MAlonzo.Code.Untyped.Relation.du_run'63'_74 (coe v0)
      (coe d_reduce_436)
-- VerifiedCompilation.UCaseReduce.norm
d_norm_444 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14
d_norm_444 v0 v1
  = coe
      MAlonzo.Code.Untyped.Transform.d__'8593''63'__68
      (coe d_reduceM_440) (coe v0) (coe v1)
-- VerifiedCompilation.UCaseReduce.reduceM-CaseReduce
d_reduceM'45'CaseReduce_448 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Untyped.Relation.T_Mu_36
d_reduceM'45'CaseReduce_448 v0
  = coe
      MAlonzo.Code.Untyped.Relation.Properties.du_Refines'63''45''8838'_152
      (\ v1 v2 v3 v4 -> coe du_red'8838'cr_454 v4)
      (\ v1 v2 v3 v4 ->
         coe
           MAlonzo.Code.Untyped.Relation.du_run'63''45'refines_98
           (coe d_reduce_436) v1 v2)
      (coe v0)
-- VerifiedCompilation.UCaseReduce._.red⊆cr
d_red'8838'cr_454 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.Relation.T__'43'__10 ->
  MAlonzo.Code.Untyped.Relation.T_Mu_36
d_red'8838'cr_454 ~v0 ~v1 ~v2 ~v3 v4 = du_red'8838'cr_454 v4
du_red'8838'cr_454 ::
  MAlonzo.Code.Untyped.Relation.T__'43'__10 ->
  MAlonzo.Code.Untyped.Relation.T_Mu_36
du_red'8838'cr_454 v0
  = coe
      MAlonzo.Code.Untyped.Relation.C_fix_46
      (coe MAlonzo.Code.Untyped.Relation.C_inl_24 v0)
-- VerifiedCompilation.UCaseReduce.norm-CaseReduce
d_norm'45'CaseReduce_456 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.Relation.T_Mu_36
d_norm'45'CaseReduce_456 v0 v1
  = coe
      MAlonzo.Code.Untyped.Transform.du_'8593''63''45'relating_270
      (coe
         (\ v2 v3 v4 v5 v6 v7 ->
            coe
              MAlonzo.Code.Untyped.Relation.C_fix_46
              (coe
                 MAlonzo.Code.Untyped.Relation.C_inr_32
                 (coe
                    MAlonzo.Code.Untyped.Relation.C_inr_32
                    (coe
                       MAlonzo.Code.Untyped.Relation.C_inl_24
                       (coe
                          MAlonzo.Code.Untyped.Relation.Composable.C_transF_162 v4 v6
                          v7))))))
      (coe d_cr'45'termcompat_208) (coe d_reduceM_440)
      (coe d_reduceM'45'CaseReduce_448) (coe v0) (coe v1)
-- VerifiedCompilation.UCaseReduce.norm*
d_norm'42'_472 ::
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14]
d_norm'42'_472 v0 v1
  = coe
      MAlonzo.Code.Untyped.Transform.d__'8593''63''42'__74
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Untyped.Relation.du_run'63'_74 (coe v2)
              (coe d_reduce_436)))
      (coe v0) (coe v1)
-- VerifiedCompilation.UCaseReduce.sound-norm-norm
d_sound'45'norm'45'norm_482 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Untyped.Relation.T_Mu_36
d_sound'45'norm'45'norm_482 v0 v1 v2 ~v3
  = du_sound'45'norm'45'norm_482 v0 v1 v2
du_sound'45'norm'45'norm_482 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.Relation.T_Mu_36
du_sound'45'norm'45'norm_482 v0 v1 v2
  = coe
      MAlonzo.Code.Untyped.Relation.C_fix_46
      (coe
         MAlonzo.Code.Untyped.Relation.C_inr_32
         (coe
            MAlonzo.Code.Untyped.Relation.C_inr_32
            (coe
               MAlonzo.Code.Untyped.Relation.C_inl_24
               (coe
                  MAlonzo.Code.Untyped.Relation.Composable.C_transF_162
                  (d_norm_444 (coe v0) (coe v1))
                  (d_norm'45'CaseReduce_456 (coe v0) (coe v1))
                  (coe
                     MAlonzo.Code.Untyped.Relation.C_fix_46
                     (coe
                        MAlonzo.Code.Untyped.Relation.C_inr_32
                        (coe
                           MAlonzo.Code.Untyped.Relation.C_inr_32
                           (coe
                              MAlonzo.Code.Untyped.Relation.C_inl_24
                              (coe
                                 MAlonzo.Code.Untyped.Relation.Composable.C_transF_162
                                 (d_norm_444 (coe v0) (coe v2)) (coe du_cr'45'refl''_200)
                                 (coe
                                    MAlonzo.Code.Untyped.Relation.C_fix_46
                                    (coe
                                       MAlonzo.Code.Untyped.Relation.C_inr_32
                                       (coe
                                          MAlonzo.Code.Untyped.Relation.C_inr_32
                                          (coe
                                             MAlonzo.Code.Untyped.Relation.C_inr_32
                                             (coe
                                                MAlonzo.Code.Untyped.Relation.C_inl_24
                                                (coe
                                                   MAlonzo.Code.Untyped.Relation.Composable.C_symF_176
                                                   (d_norm'45'CaseReduce_456
                                                      (coe v0) (coe v2)))))))))))))))))
-- VerifiedCompilation.UCaseReduce.sound-norm
d_sound'45'norm_492 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Untyped.Relation.T_Mu_36
d_sound'45'norm_492 v0 v1 ~v2 ~v3 = du_sound'45'norm_492 v0 v1
du_sound'45'norm_492 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.Relation.T_Mu_36
du_sound'45'norm_492 v0 v1
  = coe
      MAlonzo.Code.Untyped.Relation.C_fix_46
      (coe
         MAlonzo.Code.Untyped.Relation.C_inr_32
         (coe
            MAlonzo.Code.Untyped.Relation.C_inr_32
            (coe
               MAlonzo.Code.Untyped.Relation.C_inl_24
               (coe
                  MAlonzo.Code.Untyped.Relation.Composable.C_transF_162
                  (d_norm_444 (coe v0) (coe v1))
                  (d_norm'45'CaseReduce_456 (coe v0) (coe v1))
                  (coe du_cr'45'refl''_200)))))
-- VerifiedCompilation.UCaseReduce.check
d_check_502 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Maybe MAlonzo.Code.Untyped.Relation.T_Mu_36
d_check_502 v0 v1 v2
  = let v3
          = MAlonzo.Code.Untyped.Equality.d_decEq'45''8866'_56
              (coe v0)
              (coe
                 MAlonzo.Code.Data.Maybe.Base.du_maybe_32 (coe (\ v3 -> v3))
                 (coe
                    MAlonzo.Code.Untyped.Transform.d_sub_80
                    (coe
                       (\ v3 ->
                          coe
                            MAlonzo.Code.Untyped.Relation.du_run'63'_74 (coe v3)
                            (coe d_reduce_436)))
                    (coe v0) (coe v1))
                 (let v3
                        = coe
                            MAlonzo.Code.Untyped.Transform.du_'46'extendedlambda1_100
                            (coe
                               (\ v3 ->
                                  coe
                                    MAlonzo.Code.Untyped.Relation.du_run'63'_74 (coe v3)
                                    (coe d_reduce_436)))
                            (coe v0) (coe v1) in
                  coe
                    (let v4
                           = coe
                               MAlonzo.Code.Untyped.Relation.du__'60''124''62'__124
                               (\ v4 v5 -> coe du_red'45'unit_268 v5)
                               (coe
                                  MAlonzo.Code.Untyped.Relation.du__'60''124''62'__124
                                  (\ v4 v5 -> coe du_red'45'false'8321'_284 v5)
                                  (coe
                                     MAlonzo.Code.Untyped.Relation.du__'60''124''62'__124
                                     (\ v4 v5 -> coe du_red'45'bool_298 v5)
                                     (coe
                                        MAlonzo.Code.Untyped.Relation.du__'60''124''62'__124
                                        (\ v4 v5 -> coe du_red'45'integer_316 v5)
                                        (coe
                                           MAlonzo.Code.Untyped.Relation.du__'60''124''62'__124
                                           (\ v4 v5 -> coe du_red'45'cons'8321'_352 v5)
                                           (coe
                                              MAlonzo.Code.Untyped.Relation.du__'60''124''62'__124
                                              (\ v4 v5 -> coe du_red'45'cons'8322'_374 v5)
                                              (coe
                                                 MAlonzo.Code.Untyped.Relation.du__'60''124''62'__124
                                                 (\ v4 v5 -> coe du_red'45'nil_396 v5)
                                                 (\ v4 v5 -> coe du_red'45'pair_414 v5))))))) in
                     coe
                       (let v5
                              = coe
                                  MAlonzo.Code.Untyped.Transform.du_'46'extendedlambda1_100
                                  (coe
                                     (\ v5 ->
                                        coe
                                          MAlonzo.Code.Untyped.Relation.du_run'63'_74 (coe v5)
                                          (coe d_reduce_436)))
                                  (coe v0) (coe v1) in
                        coe
                          (let v6
                                 = coe
                                     MAlonzo.Code.Untyped.Transform.du_'46'extendedlambda1_100
                                     (coe
                                        (\ v6 ->
                                           coe
                                             MAlonzo.Code.Untyped.Relation.du_run'63'_74 (coe v6)
                                             (coe d_reduce_436)))
                                     (coe v0) (coe v1) in
                           coe
                             (let v7
                                    = coe
                                        MAlonzo.Code.VerifiedCompilation.UntypedViews.du_constr'63'_1618
                                        (\ v7 ->
                                           coe
                                             MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)
                                        (\ v7 ->
                                           coe
                                             MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158) in
                              coe
                                (let v8
                                       = \ v8 ->
                                           coe
                                             MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158 in
                                 coe
                                   (case coe v6 of
                                      MAlonzo.Code.Untyped.C_'96'_18 v9
                                        -> let v10 = coe v4 v0 v3 in
                                           coe
                                             (case coe v10 of
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                  -> case coe v11 of
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                         -> coe
                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                              (coe v12)
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                  -> case coe v10 of
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                         -> case coe v11 of
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                                -> coe
                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                     (coe v12)
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                         -> coe v10
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                      MAlonzo.Code.Untyped.C_ƛ_20 v9
                                        -> let v10 = coe v4 v0 v3 in
                                           coe
                                             (case coe v10 of
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                  -> case coe v11 of
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                         -> coe
                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                              (coe v12)
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                  -> case coe v10 of
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                         -> case coe v11 of
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                                -> coe
                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                     (coe v12)
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                         -> coe v10
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                      MAlonzo.Code.Untyped.C__'183'__22 v9 v10
                                        -> let v11 = coe v4 v0 v3 in
                                           coe
                                             (case coe v11 of
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                  -> case coe v12 of
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                         -> coe
                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                              (coe v13)
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                  -> case coe v11 of
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                         -> case coe v12 of
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                -> coe
                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                     (coe v13)
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                         -> coe v11
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                      MAlonzo.Code.Untyped.C_force_24 v9
                                        -> let v10 = coe v4 v0 v3 in
                                           coe
                                             (case coe v10 of
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                  -> case coe v11 of
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                         -> coe
                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                              (coe v12)
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                  -> case coe v10 of
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                         -> case coe v11 of
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                                -> coe
                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                     (coe v12)
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                         -> coe v10
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                      MAlonzo.Code.Untyped.C_delay_26 v9
                                        -> let v10 = coe v4 v0 v3 in
                                           coe
                                             (case coe v10 of
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                  -> case coe v11 of
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                         -> coe
                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                              (coe v12)
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                  -> case coe v10 of
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                         -> case coe v11 of
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                                -> coe
                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                     (coe v12)
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                         -> coe v10
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                      MAlonzo.Code.Untyped.C_con_28 v9
                                        -> let v10 = coe v4 v0 v3 in
                                           coe
                                             (case coe v10 of
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                  -> case coe v11 of
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                         -> coe
                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                              (coe v12)
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                  -> case coe v10 of
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                         -> case coe v11 of
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                                -> coe
                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                     (coe v12)
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                         -> coe v10
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                      MAlonzo.Code.Untyped.C_constr_34 v9 v10
                                        -> let v11 = coe v4 v0 v3 in
                                           coe
                                             (case coe v11 of
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                  -> case coe v12 of
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                         -> coe
                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                              (coe v13)
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                  -> case coe v11 of
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                         -> case coe v12 of
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                -> coe
                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                     (coe v13)
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                         -> coe v11
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                      MAlonzo.Code.Untyped.C_case_40 v9 v10
                                        -> let v11
                                                 = coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                                                     (coe v7 v9) (coe v8 v10) in
                                           coe
                                             (case coe v11 of
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                                  -> if coe v12
                                                       then case coe v13 of
                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v14
                                                                -> case coe v14 of
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                       -> case coe v5 of
                                                                            MAlonzo.Code.Untyped.C_case_40 v17 v18
                                                                              -> case coe v15 of
                                                                                   MAlonzo.Code.VerifiedCompilation.UntypedViews.C_constr'33'_954 v21 v22
                                                                                     -> case coe
                                                                                               v17 of
                                                                                          MAlonzo.Code.Untyped.C_constr_34 v23 v24
                                                                                            -> let v25
                                                                                                     = seq
                                                                                                         (coe
                                                                                                            v21)
                                                                                                         (coe
                                                                                                            seq
                                                                                                            (coe
                                                                                                               v22)
                                                                                                            (coe
                                                                                                               seq
                                                                                                               (coe
                                                                                                                  v16)
                                                                                                               (let v25
                                                                                                                      = coe
                                                                                                                          MAlonzo.Code.Untyped.CEK.du_lookup'63'_996
                                                                                                                          (coe
                                                                                                                             v23)
                                                                                                                          (coe
                                                                                                                             v18) in
                                                                                                                coe
                                                                                                                  (case coe
                                                                                                                          v25 of
                                                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v26
                                                                                                                       -> coe
                                                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                            (coe
                                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                               (coe
                                                                                                                                  MAlonzo.Code.Untyped.Reduction.du_iterApp_242
                                                                                                                                  (coe
                                                                                                                                     v26)
                                                                                                                                  (coe
                                                                                                                                     v24))
                                                                                                                               (coe
                                                                                                                                  C_case'45'constr_38
                                                                                                                                  v26))
                                                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                       -> coe
                                                                                                                            v25
                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError)))) in
                                                                                               coe
                                                                                                 (case coe
                                                                                                         v25 of
                                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v26
                                                                                                      -> case coe
                                                                                                                v26 of
                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v27 v28
                                                                                                             -> coe
                                                                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                  (coe
                                                                                                                     v27)
                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                      -> let v26
                                                                                                               = coe
                                                                                                                   v4
                                                                                                                   v0
                                                                                                                   v3 in
                                                                                                         coe
                                                                                                           (case coe
                                                                                                                   v26 of
                                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v27
                                                                                                                -> case coe
                                                                                                                          v27 of
                                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v28 v29
                                                                                                                       -> coe
                                                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                            (coe
                                                                                                                               v28)
                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                -> case coe
                                                                                                                          v26 of
                                                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v27
                                                                                                                       -> case coe
                                                                                                                                 v27 of
                                                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v28 v29
                                                                                                                              -> coe
                                                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                   (coe
                                                                                                                                      v28)
                                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                       -> coe
                                                                                                                            v26
                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       else (let v14
                                                                   = seq
                                                                       (coe v13)
                                                                       (coe
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                          (coe v12)
                                                                          (coe
                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                                             coe
                                                               (case coe v14 of
                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                                                    -> if coe v15
                                                                         then case coe v16 of
                                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v17
                                                                                  -> case coe v17 of
                                                                                       MAlonzo.Code.VerifiedCompilation.UntypedViews.C_case'33'_936 v20 v21
                                                                                         -> case coe
                                                                                                   v5 of
                                                                                              MAlonzo.Code.Untyped.C_case_40 v22 v23
                                                                                                -> case coe
                                                                                                          v20 of
                                                                                                     MAlonzo.Code.VerifiedCompilation.UntypedViews.C_constr'33'_954 v26 v27
                                                                                                       -> case coe
                                                                                                                 v22 of
                                                                                                            MAlonzo.Code.Untyped.C_constr_34 v28 v29
                                                                                                              -> let v30
                                                                                                                       = seq
                                                                                                                           (coe
                                                                                                                              v26)
                                                                                                                           (coe
                                                                                                                              seq
                                                                                                                              (coe
                                                                                                                                 v27)
                                                                                                                              (coe
                                                                                                                                 seq
                                                                                                                                 (coe
                                                                                                                                    v21)
                                                                                                                                 (let v30
                                                                                                                                        = coe
                                                                                                                                            MAlonzo.Code.Untyped.CEK.du_lookup'63'_996
                                                                                                                                            (coe
                                                                                                                                               v28)
                                                                                                                                            (coe
                                                                                                                                               v23) in
                                                                                                                                  coe
                                                                                                                                    (case coe
                                                                                                                                            v30 of
                                                                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v31
                                                                                                                                         -> coe
                                                                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                              (coe
                                                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                 (coe
                                                                                                                                                    MAlonzo.Code.Untyped.Reduction.du_iterApp_242
                                                                                                                                                    (coe
                                                                                                                                                       v31)
                                                                                                                                                    (coe
                                                                                                                                                       v29))
                                                                                                                                                 (coe
                                                                                                                                                    C_case'45'constr_38
                                                                                                                                                    v31))
                                                                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                         -> coe
                                                                                                                                              v30
                                                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError)))) in
                                                                                                                 coe
                                                                                                                   (case coe
                                                                                                                           v30 of
                                                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v31
                                                                                                                        -> case coe
                                                                                                                                  v31 of
                                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v32 v33
                                                                                                                               -> coe
                                                                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                    (coe
                                                                                                                                       v32)
                                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                        -> let v31
                                                                                                                                 = coe
                                                                                                                                     v4
                                                                                                                                     v0
                                                                                                                                     v3 in
                                                                                                                           coe
                                                                                                                             (case coe
                                                                                                                                     v31 of
                                                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v32
                                                                                                                                  -> case coe
                                                                                                                                            v32 of
                                                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v33 v34
                                                                                                                                         -> coe
                                                                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                              (coe
                                                                                                                                                 v33)
                                                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                  -> case coe
                                                                                                                                            v31 of
                                                                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v32
                                                                                                                                         -> case coe
                                                                                                                                                   v32 of
                                                                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v33 v34
                                                                                                                                                -> coe
                                                                                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                     (coe
                                                                                                                                                        v33)
                                                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                         -> coe
                                                                                                                                              v31
                                                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                         else (let v17
                                                                                     = seq
                                                                                         (coe v16)
                                                                                         (coe
                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18) in
                                                                               coe
                                                                                 (case coe v17 of
                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v18
                                                                                      -> case coe
                                                                                                v18 of
                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                                             -> coe
                                                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                  (coe
                                                                                                     v19)
                                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                      -> let v18
                                                                                               = coe
                                                                                                   v4
                                                                                                   v0
                                                                                                   v3 in
                                                                                         coe
                                                                                           (case coe
                                                                                                   v18 of
                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v19
                                                                                                -> case coe
                                                                                                          v19 of
                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                                                       -> coe
                                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                            (coe
                                                                                                               v20)
                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                -> case coe
                                                                                                          v18 of
                                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v19
                                                                                                       -> case coe
                                                                                                                 v19 of
                                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                                                              -> coe
                                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                   (coe
                                                                                                                      v20)
                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                       -> coe
                                                                                                            v18
                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError))
                                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                      MAlonzo.Code.Untyped.C_builtin_44 v9
                                        -> let v10 = coe v4 v0 v3 in
                                           coe
                                             (case coe v10 of
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                  -> case coe v11 of
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                         -> coe
                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                              (coe v12)
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                  -> case coe v10 of
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                         -> case coe v11 of
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                                -> coe
                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                     (coe v12)
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                         -> coe v10
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                      MAlonzo.Code.Untyped.C_error_46
                                        -> let v9 = coe v4 v0 v3 in
                                           coe
                                             (case coe v9 of
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                  -> case coe v10 of
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                         -> coe
                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                              (coe v11)
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                  -> case coe v9 of
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                         -> case coe v10 of
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                                -> coe
                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                     (coe v11)
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                         -> coe v9
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                      _ -> MAlonzo.RTE.mazUnreachableError))))))))
              (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe
                       seq (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                          (coe du_sound'45'norm_492 (coe v0) (coe v1)))
                else coe
                       seq (coe v5) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.UCaseReduce.decide
d_decide_530 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_38
d_decide_530 v0 v1 v2
  = let v3
          = MAlonzo.Code.Untyped.Equality.d_decEq'45''8866'_56
              (coe v0)
              (coe
                 MAlonzo.Code.Data.Maybe.Base.du_maybe_32 (coe (\ v3 -> v3))
                 (coe
                    MAlonzo.Code.Untyped.Transform.d_sub_80
                    (coe
                       (\ v3 ->
                          coe
                            MAlonzo.Code.Untyped.Relation.du_run'63'_74 (coe v3)
                            (coe d_reduce_436)))
                    (coe v0) (coe v1))
                 (let v3
                        = coe
                            MAlonzo.Code.Untyped.Transform.du_'46'extendedlambda1_100
                            (coe
                               (\ v3 ->
                                  coe
                                    MAlonzo.Code.Untyped.Relation.du_run'63'_74 (coe v3)
                                    (coe d_reduce_436)))
                            (coe v0) (coe v1) in
                  coe
                    (let v4
                           = coe
                               MAlonzo.Code.Untyped.Relation.du__'60''124''62'__124
                               (\ v4 v5 -> coe du_red'45'unit_268 v5)
                               (coe
                                  MAlonzo.Code.Untyped.Relation.du__'60''124''62'__124
                                  (\ v4 v5 -> coe du_red'45'false'8321'_284 v5)
                                  (coe
                                     MAlonzo.Code.Untyped.Relation.du__'60''124''62'__124
                                     (\ v4 v5 -> coe du_red'45'bool_298 v5)
                                     (coe
                                        MAlonzo.Code.Untyped.Relation.du__'60''124''62'__124
                                        (\ v4 v5 -> coe du_red'45'integer_316 v5)
                                        (coe
                                           MAlonzo.Code.Untyped.Relation.du__'60''124''62'__124
                                           (\ v4 v5 -> coe du_red'45'cons'8321'_352 v5)
                                           (coe
                                              MAlonzo.Code.Untyped.Relation.du__'60''124''62'__124
                                              (\ v4 v5 -> coe du_red'45'cons'8322'_374 v5)
                                              (coe
                                                 MAlonzo.Code.Untyped.Relation.du__'60''124''62'__124
                                                 (\ v4 v5 -> coe du_red'45'nil_396 v5)
                                                 (\ v4 v5 -> coe du_red'45'pair_414 v5))))))) in
                     coe
                       (let v5
                              = coe
                                  MAlonzo.Code.Untyped.Transform.du_'46'extendedlambda1_100
                                  (coe
                                     (\ v5 ->
                                        coe
                                          MAlonzo.Code.Untyped.Relation.du_run'63'_74 (coe v5)
                                          (coe d_reduce_436)))
                                  (coe v0) (coe v1) in
                        coe
                          (let v6
                                 = coe
                                     MAlonzo.Code.Untyped.Transform.du_'46'extendedlambda1_100
                                     (coe
                                        (\ v6 ->
                                           coe
                                             MAlonzo.Code.Untyped.Relation.du_run'63'_74 (coe v6)
                                             (coe d_reduce_436)))
                                     (coe v0) (coe v1) in
                           coe
                             (let v7
                                    = coe
                                        MAlonzo.Code.VerifiedCompilation.UntypedViews.du_constr'63'_1618
                                        (\ v7 ->
                                           coe
                                             MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)
                                        (\ v7 ->
                                           coe
                                             MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158) in
                              coe
                                (let v8
                                       = \ v8 ->
                                           coe
                                             MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158 in
                                 coe
                                   (case coe v6 of
                                      MAlonzo.Code.Untyped.C_'96'_18 v9
                                        -> let v10 = coe v4 v0 v3 in
                                           coe
                                             (case coe v10 of
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                  -> case coe v11 of
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                         -> coe
                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                              (coe v12)
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                  -> case coe v10 of
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                         -> case coe v11 of
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                                -> coe
                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                     (coe v12)
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                         -> coe v10
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                      MAlonzo.Code.Untyped.C_ƛ_20 v9
                                        -> let v10 = coe v4 v0 v3 in
                                           coe
                                             (case coe v10 of
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                  -> case coe v11 of
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                         -> coe
                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                              (coe v12)
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                  -> case coe v10 of
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                         -> case coe v11 of
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                                -> coe
                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                     (coe v12)
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                         -> coe v10
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                      MAlonzo.Code.Untyped.C__'183'__22 v9 v10
                                        -> let v11 = coe v4 v0 v3 in
                                           coe
                                             (case coe v11 of
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                  -> case coe v12 of
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                         -> coe
                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                              (coe v13)
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                  -> case coe v11 of
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                         -> case coe v12 of
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                -> coe
                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                     (coe v13)
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                         -> coe v11
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                      MAlonzo.Code.Untyped.C_force_24 v9
                                        -> let v10 = coe v4 v0 v3 in
                                           coe
                                             (case coe v10 of
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                  -> case coe v11 of
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                         -> coe
                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                              (coe v12)
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                  -> case coe v10 of
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                         -> case coe v11 of
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                                -> coe
                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                     (coe v12)
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                         -> coe v10
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                      MAlonzo.Code.Untyped.C_delay_26 v9
                                        -> let v10 = coe v4 v0 v3 in
                                           coe
                                             (case coe v10 of
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                  -> case coe v11 of
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                         -> coe
                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                              (coe v12)
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                  -> case coe v10 of
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                         -> case coe v11 of
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                                -> coe
                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                     (coe v12)
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                         -> coe v10
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                      MAlonzo.Code.Untyped.C_con_28 v9
                                        -> let v10 = coe v4 v0 v3 in
                                           coe
                                             (case coe v10 of
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                  -> case coe v11 of
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                         -> coe
                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                              (coe v12)
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                  -> case coe v10 of
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                         -> case coe v11 of
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                                -> coe
                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                     (coe v12)
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                         -> coe v10
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                      MAlonzo.Code.Untyped.C_constr_34 v9 v10
                                        -> let v11 = coe v4 v0 v3 in
                                           coe
                                             (case coe v11 of
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                  -> case coe v12 of
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                         -> coe
                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                              (coe v13)
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                  -> case coe v11 of
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                         -> case coe v12 of
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                -> coe
                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                     (coe v13)
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                         -> coe v11
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                      MAlonzo.Code.Untyped.C_case_40 v9 v10
                                        -> let v11
                                                 = coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                                                     (coe v7 v9) (coe v8 v10) in
                                           coe
                                             (case coe v11 of
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                                  -> if coe v12
                                                       then case coe v13 of
                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v14
                                                                -> case coe v14 of
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                       -> case coe v5 of
                                                                            MAlonzo.Code.Untyped.C_case_40 v17 v18
                                                                              -> case coe v15 of
                                                                                   MAlonzo.Code.VerifiedCompilation.UntypedViews.C_constr'33'_954 v21 v22
                                                                                     -> case coe
                                                                                               v17 of
                                                                                          MAlonzo.Code.Untyped.C_constr_34 v23 v24
                                                                                            -> let v25
                                                                                                     = seq
                                                                                                         (coe
                                                                                                            v21)
                                                                                                         (coe
                                                                                                            seq
                                                                                                            (coe
                                                                                                               v22)
                                                                                                            (coe
                                                                                                               seq
                                                                                                               (coe
                                                                                                                  v16)
                                                                                                               (let v25
                                                                                                                      = coe
                                                                                                                          MAlonzo.Code.Untyped.CEK.du_lookup'63'_996
                                                                                                                          (coe
                                                                                                                             v23)
                                                                                                                          (coe
                                                                                                                             v18) in
                                                                                                                coe
                                                                                                                  (case coe
                                                                                                                          v25 of
                                                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v26
                                                                                                                       -> coe
                                                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                            (coe
                                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                               (coe
                                                                                                                                  MAlonzo.Code.Untyped.Reduction.du_iterApp_242
                                                                                                                                  (coe
                                                                                                                                     v26)
                                                                                                                                  (coe
                                                                                                                                     v24))
                                                                                                                               (coe
                                                                                                                                  C_case'45'constr_38
                                                                                                                                  v26))
                                                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                       -> coe
                                                                                                                            v25
                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError)))) in
                                                                                               coe
                                                                                                 (case coe
                                                                                                         v25 of
                                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v26
                                                                                                      -> case coe
                                                                                                                v26 of
                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v27 v28
                                                                                                             -> coe
                                                                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                  (coe
                                                                                                                     v27)
                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                      -> let v26
                                                                                                               = coe
                                                                                                                   v4
                                                                                                                   v0
                                                                                                                   v3 in
                                                                                                         coe
                                                                                                           (case coe
                                                                                                                   v26 of
                                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v27
                                                                                                                -> case coe
                                                                                                                          v27 of
                                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v28 v29
                                                                                                                       -> coe
                                                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                            (coe
                                                                                                                               v28)
                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                -> case coe
                                                                                                                          v26 of
                                                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v27
                                                                                                                       -> case coe
                                                                                                                                 v27 of
                                                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v28 v29
                                                                                                                              -> coe
                                                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                   (coe
                                                                                                                                      v28)
                                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                       -> coe
                                                                                                                            v26
                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       else (let v14
                                                                   = seq
                                                                       (coe v13)
                                                                       (coe
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                          (coe v12)
                                                                          (coe
                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                                             coe
                                                               (case coe v14 of
                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                                                    -> if coe v15
                                                                         then case coe v16 of
                                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v17
                                                                                  -> case coe v17 of
                                                                                       MAlonzo.Code.VerifiedCompilation.UntypedViews.C_case'33'_936 v20 v21
                                                                                         -> case coe
                                                                                                   v5 of
                                                                                              MAlonzo.Code.Untyped.C_case_40 v22 v23
                                                                                                -> case coe
                                                                                                          v20 of
                                                                                                     MAlonzo.Code.VerifiedCompilation.UntypedViews.C_constr'33'_954 v26 v27
                                                                                                       -> case coe
                                                                                                                 v22 of
                                                                                                            MAlonzo.Code.Untyped.C_constr_34 v28 v29
                                                                                                              -> let v30
                                                                                                                       = seq
                                                                                                                           (coe
                                                                                                                              v26)
                                                                                                                           (coe
                                                                                                                              seq
                                                                                                                              (coe
                                                                                                                                 v27)
                                                                                                                              (coe
                                                                                                                                 seq
                                                                                                                                 (coe
                                                                                                                                    v21)
                                                                                                                                 (let v30
                                                                                                                                        = coe
                                                                                                                                            MAlonzo.Code.Untyped.CEK.du_lookup'63'_996
                                                                                                                                            (coe
                                                                                                                                               v28)
                                                                                                                                            (coe
                                                                                                                                               v23) in
                                                                                                                                  coe
                                                                                                                                    (case coe
                                                                                                                                            v30 of
                                                                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v31
                                                                                                                                         -> coe
                                                                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                              (coe
                                                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                 (coe
                                                                                                                                                    MAlonzo.Code.Untyped.Reduction.du_iterApp_242
                                                                                                                                                    (coe
                                                                                                                                                       v31)
                                                                                                                                                    (coe
                                                                                                                                                       v29))
                                                                                                                                                 (coe
                                                                                                                                                    C_case'45'constr_38
                                                                                                                                                    v31))
                                                                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                         -> coe
                                                                                                                                              v30
                                                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError)))) in
                                                                                                                 coe
                                                                                                                   (case coe
                                                                                                                           v30 of
                                                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v31
                                                                                                                        -> case coe
                                                                                                                                  v31 of
                                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v32 v33
                                                                                                                               -> coe
                                                                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                    (coe
                                                                                                                                       v32)
                                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                        -> let v31
                                                                                                                                 = coe
                                                                                                                                     v4
                                                                                                                                     v0
                                                                                                                                     v3 in
                                                                                                                           coe
                                                                                                                             (case coe
                                                                                                                                     v31 of
                                                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v32
                                                                                                                                  -> case coe
                                                                                                                                            v32 of
                                                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v33 v34
                                                                                                                                         -> coe
                                                                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                              (coe
                                                                                                                                                 v33)
                                                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                  -> case coe
                                                                                                                                            v31 of
                                                                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v32
                                                                                                                                         -> case coe
                                                                                                                                                   v32 of
                                                                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v33 v34
                                                                                                                                                -> coe
                                                                                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                     (coe
                                                                                                                                                        v33)
                                                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                         -> coe
                                                                                                                                              v31
                                                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                         else (let v17
                                                                                     = seq
                                                                                         (coe v16)
                                                                                         (coe
                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18) in
                                                                               coe
                                                                                 (case coe v17 of
                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v18
                                                                                      -> case coe
                                                                                                v18 of
                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                                             -> coe
                                                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                  (coe
                                                                                                     v19)
                                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                      -> let v18
                                                                                               = coe
                                                                                                   v4
                                                                                                   v0
                                                                                                   v3 in
                                                                                         coe
                                                                                           (case coe
                                                                                                   v18 of
                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v19
                                                                                                -> case coe
                                                                                                          v19 of
                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                                                       -> coe
                                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                            (coe
                                                                                                               v20)
                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                -> case coe
                                                                                                          v18 of
                                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v19
                                                                                                       -> case coe
                                                                                                                 v19 of
                                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                                                              -> coe
                                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                   (coe
                                                                                                                      v20)
                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                       -> coe
                                                                                                            v18
                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError))
                                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                      MAlonzo.Code.Untyped.C_builtin_44 v9
                                        -> let v10 = coe v4 v0 v3 in
                                           coe
                                             (case coe v10 of
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                  -> case coe v11 of
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                         -> coe
                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                              (coe v12)
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                  -> case coe v10 of
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                         -> case coe v11 of
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                                -> coe
                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                     (coe v12)
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                         -> coe v10
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                      MAlonzo.Code.Untyped.C_error_46
                                        -> let v9 = coe v4 v0 v3 in
                                           coe
                                             (case coe v9 of
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                  -> case coe v10 of
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                         -> coe
                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                              (coe v11)
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                  -> case coe v9 of
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                         -> case coe v10 of
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                                -> coe
                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                     (coe v11)
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                         -> coe v9
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                      _ -> MAlonzo.RTE.mazUnreachableError))))))))
              (coe d_norm_444 (coe v0) (coe v2)) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then case coe v5 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v6
                         -> coe
                              MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_44 (coe v6)
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v5)
                       (coe
                          MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52
                          (coe MAlonzo.Code.VerifiedCompilation.Trace.C_caseReduceT_14) v1
                          v2)
         _ -> MAlonzo.RTE.mazUnreachableError)
