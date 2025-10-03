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

module MAlonzo.Code.Untyped.Purity where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Builtin
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.RawU
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects
import qualified MAlonzo.Code.Untyped
import qualified MAlonzo.Code.Untyped.CEK
import qualified MAlonzo.Code.Untyped.Reduction
import qualified MAlonzo.Code.VerifiedCompilation.UntypedViews

-- Untyped.Purity.Pure
d_Pure_6 a0 a1 = ()
data T_Pure_6
  = C_force_12 T_Pure_6 |
    C_constr_18 MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 |
    C_case_28 MAlonzo.Code.Untyped.T__'8866'_14 T_Pure_6 |
    C_builtin_32 |
    C_unsat'45'builtin'8320'_40 Integer Integer T_Pure_6 |
    C_unsat'45'builtin'8320''8331''8321'_46 Integer T_Pure_6 |
    C_unsat'45'builtin'8321'_54 Integer T_Pure_6 T_Pure_6 |
    C_app_60 T_Pure_6 T_Pure_6 | C_var_64 | C_delay_68 | C_ƛ_72 |
    C_con_76
-- Untyped.Purity.isPure?
d_isPure'63'_82 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_isPure'63'_82 ~v0 v1 = du_isPure'63'_82 v1
du_isPure'63'_82 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_isPure'63'_82 v0
  = case coe v0 of
      MAlonzo.Code.Untyped.C_'96'_18 v1
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 (coe C_var_64))
      MAlonzo.Code.Untyped.C_ƛ_20 v1
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 (coe C_ƛ_72))
      MAlonzo.Code.Untyped.C__'183'__22 v1 v2
        -> let v3
                 = coe
                     MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isLambda'63'_70
                     (\ v3 v4 ->
                        coe
                          MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)
                     (coe v1) in
           coe
             (case coe v3 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                  -> if coe v4
                       then case coe v5 of
                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v6
                                -> case coe v6 of
                                     MAlonzo.Code.VerifiedCompilation.UntypedViews.C_islambda_62 v8
                                       -> case coe v1 of
                                            MAlonzo.Code.Untyped.C_ƛ_20 v9
                                              -> coe
                                                   seq (coe v8)
                                                   (let v10
                                                          = coe
                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__76
                                                              (coe du_isPure'63'_82 (coe v9))
                                                              (coe du_isPure'63'_82 (coe v2)) in
                                                    coe
                                                      (case coe v10 of
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                                           -> if coe v11
                                                                then case coe v12 of
                                                                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v13
                                                                         -> case coe v13 of
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                                                -> coe
                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                     (coe v11)
                                                                                     (coe
                                                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                        (coe
                                                                                           C_app_60
                                                                                           v14 v15))
                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                else coe
                                                                       seq (coe v12)
                                                                       (coe
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                          (coe v11)
                                                                          (coe
                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                         _ -> MAlonzo.RTE.mazUnreachableError))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       else coe
                              seq (coe v5)
                              (let v6 = coe MAlonzo.Code.Untyped.Reduction.du_sat_36 (coe v1) in
                               coe
                                 (case coe v6 of
                                    MAlonzo.Code.Untyped.Reduction.C_no'45'builtin_6
                                      -> coe
                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                           (coe v4)
                                           (coe
                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                    MAlonzo.Code.Untyped.Reduction.C_want_8 v7 v8
                                      -> case coe v7 of
                                           0 -> case coe v8 of
                                                  0 -> coe
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                         (coe v4)
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                  1 -> coe
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                         (coe v4)
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                  _ -> let v9
                                                             = subInt
                                                                 (coe v8) (coe (2 :: Integer)) in
                                                       coe
                                                         (let v10
                                                                = coe
                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__76
                                                                    (coe du_isPure'63'_82 (coe v1))
                                                                    (coe
                                                                       du_isPure'63'_82 (coe v2)) in
                                                          coe
                                                            (case coe v10 of
                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                                                 -> if coe v11
                                                                      then case coe v12 of
                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v13
                                                                               -> case coe v13 of
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                                                      -> coe
                                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                           (coe v11)
                                                                                           (coe
                                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                              (coe
                                                                                                 C_unsat'45'builtin'8321'_54
                                                                                                 v9
                                                                                                 v14
                                                                                                 v15))
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                      else coe
                                                                             seq (coe v12)
                                                                             (coe
                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                (coe v11)
                                                                                (coe
                                                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                           _ -> coe
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                  (coe v4)
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Untyped.C_force_24 v1
        -> let v2
                 = coe
                     MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isDelay'63'_370
                     erased
                     (\ v2 v3 ->
                        coe
                          MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)
                     (coe v1) in
           coe
             (case coe v2 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
                  -> if coe v3
                       then case coe v4 of
                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v5
                                -> case coe v5 of
                                     MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isdelay_362 v7
                                       -> case coe v1 of
                                            MAlonzo.Code.Untyped.C_delay_26 v8
                                              -> coe
                                                   seq (coe v7)
                                                   (let v9 = coe du_isPure'63'_82 (coe v8) in
                                                    coe
                                                      (case coe v9 of
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                                           -> if coe v10
                                                                then case coe v11 of
                                                                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v12
                                                                         -> coe
                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                              (coe v10)
                                                                              (coe
                                                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                 (coe
                                                                                    C_force_12 v12))
                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                else coe
                                                                       seq (coe v11)
                                                                       (coe
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                          (coe v10)
                                                                          (coe
                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                         _ -> MAlonzo.RTE.mazUnreachableError))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       else coe
                              seq (coe v4)
                              (let v5 = coe MAlonzo.Code.Untyped.Reduction.du_sat_36 (coe v1) in
                               coe
                                 (case coe v5 of
                                    MAlonzo.Code.Untyped.Reduction.C_no'45'builtin_6
                                      -> coe
                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                           (coe v3)
                                           (coe
                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                    MAlonzo.Code.Untyped.Reduction.C_want_8 v6 v7
                                      -> case coe v6 of
                                           0 -> coe
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                  (coe v3)
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                           1 -> case coe v7 of
                                                  0 -> coe
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                         (coe v3)
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                  _ -> let v8
                                                             = subInt
                                                                 (coe v7) (coe (1 :: Integer)) in
                                                       coe
                                                         (let v9 = coe du_isPure'63'_82 (coe v1) in
                                                          coe
                                                            (case coe v9 of
                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                                                 -> if coe v10
                                                                      then case coe v11 of
                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v12
                                                                               -> coe
                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                    (coe v10)
                                                                                    (coe
                                                                                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                       (coe
                                                                                          C_unsat'45'builtin'8320''8331''8321'_46
                                                                                          v8 v12))
                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                      else coe
                                                                             seq (coe v11)
                                                                             (coe
                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                (coe v10)
                                                                                (coe
                                                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                           _ -> let v8 = subInt (coe v6) (coe (2 :: Integer)) in
                                                coe
                                                  (let v9 = coe du_isPure'63'_82 (coe v1) in
                                                   coe
                                                     (case coe v9 of
                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                                          -> if coe v10
                                                               then case coe v11 of
                                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v12
                                                                        -> coe
                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                             (coe v10)
                                                                             (coe
                                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                (coe
                                                                                   C_unsat'45'builtin'8320'_40
                                                                                   v8 v7 v12))
                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                               else coe
                                                                      seq (coe v11)
                                                                      (coe
                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                         (coe v10)
                                                                         (coe
                                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                        _ -> MAlonzo.RTE.mazUnreachableError))
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Untyped.C_delay_26 v1
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                (coe C_delay_68))
      MAlonzo.Code.Untyped.C_con_28 v1
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 (coe C_con_76))
      MAlonzo.Code.Untyped.C_constr_34 v1 v2
        -> let v3 = coe du_allPure'63'_88 (coe v2) in
           coe
             (case coe v3 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                  -> if coe v4
                       then case coe v5 of
                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v6
                                -> coe
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                     (coe v4)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                        (coe C_constr_18 v6))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       else coe
                              seq (coe v5)
                              (coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                 (coe v4)
                                 (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Untyped.C_case_40 v1 v2
        -> case coe v1 of
             MAlonzo.Code.Untyped.C_'96'_18 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_ƛ_20 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C__'183'__22 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_force_24 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_delay_26 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_con_28 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_constr_34 v3 v4
               -> let v5
                        = coe
                            MAlonzo.Code.Untyped.CEK.du_lookup'63'_988 (coe v3) (coe v2) in
                  coe
                    (case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                         -> let v7
                                  = coe
                                      du_isPure'63'_82
                                      (coe
                                         MAlonzo.Code.Untyped.Reduction.du_iterApp_242 (coe v6)
                                         (coe v4)) in
                            coe
                              (case coe v7 of
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                   -> if coe v8
                                        then case coe v9 of
                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v10
                                                 -> coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                      (coe v8)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                         (coe C_case_28 v6 v10))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        else coe
                                               seq (coe v9)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                  (coe v8)
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                         -> coe
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                              (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                              (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Untyped.C_case_40 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_builtin_44 v3
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
      MAlonzo.Code.Untyped.C_builtin_44 v1
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                (coe C_builtin_32))
      MAlonzo.Code.Untyped.C_error_46
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Purity.allPure?
d_allPure'63'_88 ::
  () ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_allPure'63'_88 ~v0 v1 = du_allPure'63'_88 v1
du_allPure'63'_88 ::
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_allPure'63'_88 v0
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
      (:) v1 v2
        -> let v3
                 = coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__76
                     (coe du_isPure'63'_82 (coe v1)) (coe du_allPure'63'_88 (coe v2)) in
           coe
             (case coe v3 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                  -> if coe v4
                       then case coe v5 of
                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v6
                                -> case coe v6 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                       -> coe
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                            (coe v4)
                                            (coe
                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                               (coe
                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                  v7 v8))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       else coe
                              seq (coe v5)
                              (coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                 (coe v4)
                                 (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Purity..extendedlambda0
d_'46'extendedlambda0_112 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda0_112 = erased
-- Untyped.Purity..extendedlambda1
d_'46'extendedlambda1_158 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_Pure_6 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda1_158 = erased
-- Untyped.Purity..extendedlambda2
d_'46'extendedlambda2_182 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isLambda_54 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  T_Pure_6 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda2_182 = erased
-- Untyped.Purity..extendedlambda3
d_'46'extendedlambda3_200 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isLambda_54 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  T_Pure_6 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda3_200 = erased
-- Untyped.Purity..extendedlambda4
d_'46'extendedlambda4_214 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isLambda_54 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  T_Pure_6 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda4_214 = erased
-- Untyped.Purity..extendedlambda5
d_'46'extendedlambda5_232 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isLambda_54 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  T_Pure_6 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda5_232 = erased
-- Untyped.Purity..extendedlambda6
d_'46'extendedlambda6_274 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isLambda_54 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_Pure_6 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda6_274 = erased
-- Untyped.Purity..extendedlambda7
d_'46'extendedlambda7_302 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isDelay_354 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_Pure_6 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda7_302 = erased
-- Untyped.Purity..extendedlambda8
d_'46'extendedlambda8_320 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isDelay_354 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_Pure_6 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda8_320 = erased
-- Untyped.Purity..extendedlambda9
d_'46'extendedlambda9_334 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isDelay_354 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_Pure_6 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda9_334 = erased
-- Untyped.Purity..extendedlambda10
d_'46'extendedlambda10_362 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (T_Pure_6 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isDelay_354 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_Pure_6 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda10_362 = erased
-- Untyped.Purity..extendedlambda11
d_'46'extendedlambda11_402 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (T_Pure_6 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isDelay_354 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_Pure_6 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda11_402 = erased
-- Untyped.Purity..extendedlambda12
d_'46'extendedlambda12_442 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (T_Pure_6 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_Pure_6 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda12_442 = erased
-- Untyped.Purity..extendedlambda13
d_'46'extendedlambda13_470 ::
  () ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  (MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  Integer -> T_Pure_6 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda13_470 = erased
-- Untyped.Purity..extendedlambda14
d_'46'extendedlambda14_518 ::
  () ->
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  T_Pure_6 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda14_518 = erased
-- Untyped.Purity..extendedlambda15
d_'46'extendedlambda15_556 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  (T_Pure_6 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Pure_6 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda15_556 = erased
