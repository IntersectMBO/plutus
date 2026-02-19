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

module MAlonzo.Code.VerifiedCompilation.UFloatDelay where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Builtin
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Fin.Properties
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.RawU
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects
import qualified MAlonzo.Code.Untyped
import qualified MAlonzo.Code.Untyped.Purity
import qualified MAlonzo.Code.VerifiedCompilation.Certificate
import qualified MAlonzo.Code.VerifiedCompilation.UntypedTranslation
import qualified MAlonzo.Code.VerifiedCompilation.UntypedViews

-- VerifiedCompilation.UFloatDelay.AllForced
d_AllForced_16 a0 a1 a2 = ()
data T_AllForced_16
  = C_var_24 | C_forced_28 | C_force_32 T_AllForced_16 |
    C_delay_36 T_AllForced_16 | C_ƛ_42 T_AllForced_16 |
    C_app_46 T_AllForced_16 T_AllForced_16 | C_error_50 |
    C_builtin_56 | C_con_62 |
    C_case_70 T_AllForced_16
              MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 |
    C_constr_78 MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
-- VerifiedCompilation.UFloatDelay.isAllForced?
d_isAllForced'63'_84 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_isAllForced'63'_84 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isForce'63'_284
              (coe v0)
              (\ v3 v4 ->
                 coe
                   MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)
              (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then case coe v5 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v6
                         -> case coe v6 of
                              MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isforce_276 v8
                                -> case coe v2 of
                                     MAlonzo.Code.Untyped.C_force_24 v9
                                       -> coe
                                            seq (coe v8)
                                            (let v10
                                                   = coe
                                                       MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isVar'63'_24
                                                       (coe v9) in
                                             coe
                                               (case coe v10 of
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                                    -> if coe v11
                                                         then case coe v12 of
                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v13
                                                                  -> coe
                                                                       seq (coe v13)
                                                                       (case coe v9 of
                                                                          MAlonzo.Code.Untyped.C_'96'_18 v14
                                                                            -> let v15
                                                                                     = coe
                                                                                         MAlonzo.Code.Data.Fin.Properties.du__'8799'__50
                                                                                         (coe v14)
                                                                                         (coe v1) in
                                                                               coe
                                                                                 (case coe v15 of
                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                                      -> if coe v16
                                                                                           then coe
                                                                                                  seq
                                                                                                  (coe
                                                                                                     v17)
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                     (coe
                                                                                                        v16)
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                        (coe
                                                                                                           C_forced_28)))
                                                                                           else coe
                                                                                                  seq
                                                                                                  (coe
                                                                                                     v17)
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                     (coe
                                                                                                        v11)
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                        (coe
                                                                                                           C_force_32
                                                                                                           (coe
                                                                                                              C_var_24))))
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         else coe
                                                                seq (coe v12)
                                                                (let v13
                                                                       = d_isAllForced'63'_84
                                                                           (coe v0) (coe v1)
                                                                           (coe v9) in
                                                                 coe
                                                                   (case coe v13 of
                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                                        -> if coe v14
                                                                             then case coe v15 of
                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v16
                                                                                      -> coe
                                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                           (coe v14)
                                                                                           (coe
                                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                              (coe
                                                                                                 C_force_32
                                                                                                 v16))
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                             else coe
                                                                                    seq (coe v15)
                                                                                    (coe
                                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                       (coe v14)
                                                                                       (coe
                                                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                else (case coe v2 of
                        MAlonzo.Code.Untyped.C_'96'_18 v6
                          -> coe
                               seq (coe v5)
                               (let v7
                                      = coe
                                          MAlonzo.Code.Data.Fin.Properties.du__'8799'__50 (coe v6)
                                          (coe v1) in
                                coe
                                  (case coe v7 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                       -> if coe v8
                                            then coe
                                                   seq (coe v9)
                                                   (coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                      (coe v4)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                            else coe
                                                   seq (coe v9)
                                                   (coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                         (coe C_var_24)))
                                     _ -> MAlonzo.RTE.mazUnreachableError))
                        MAlonzo.Code.Untyped.C_ƛ_20 v6
                          -> coe
                               seq (coe v5)
                               (let v7
                                      = d_isAllForced'63'_84
                                          (coe addInt (coe (1 :: Integer)) (coe v0))
                                          (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v1) (coe v6) in
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
                                                             (coe C_ƛ_42 v10))
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            else coe
                                                   seq (coe v9)
                                                   (coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                      (coe v8)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                     _ -> MAlonzo.RTE.mazUnreachableError))
                        MAlonzo.Code.Untyped.C__'183'__22 v6 v7
                          -> coe
                               seq (coe v5)
                               (let v8
                                      = coe
                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__76
                                          (coe d_isAllForced'63'_84 (coe v0) (coe v1) (coe v6))
                                          (coe d_isAllForced'63'_84 (coe v0) (coe v1) (coe v7)) in
                                coe
                                  (case coe v8 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                       -> if coe v9
                                            then case coe v10 of
                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v11
                                                     -> case coe v11 of
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                            -> coe
                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                 (coe v9)
                                                                 (coe
                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                    (coe C_app_46 v12 v13))
                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            else coe
                                                   seq (coe v10)
                                                   (coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                      (coe v9)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                     _ -> MAlonzo.RTE.mazUnreachableError))
                        MAlonzo.Code.Untyped.C_force_24 v6
                          -> coe
                               seq (coe v5)
                               (coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                  (coe v4)
                                  (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                        MAlonzo.Code.Untyped.C_delay_26 v6
                          -> coe
                               seq (coe v5)
                               (let v7 = d_isAllForced'63'_84 (coe v0) (coe v1) (coe v6) in
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
                                                             (coe C_delay_36 v10))
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            else coe
                                                   seq (coe v9)
                                                   (coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                      (coe v8)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                     _ -> MAlonzo.RTE.mazUnreachableError))
                        MAlonzo.Code.Untyped.C_con_28 v6
                          -> coe
                               seq (coe v5)
                               (coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                                  (coe
                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                     (coe C_con_62)))
                        MAlonzo.Code.Untyped.C_constr_34 v6 v7
                          -> coe
                               seq (coe v5)
                               (let v8
                                      = coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.du_all'63'_506
                                          (coe d_isAllForced'63'_84 (coe v0) (coe v1)) (coe v7) in
                                coe
                                  (case coe v8 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                       -> if coe v9
                                            then case coe v10 of
                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v11
                                                     -> coe
                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                          (coe v9)
                                                          (coe
                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                             (coe C_constr_78 v11))
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            else coe
                                                   seq (coe v10)
                                                   (coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                      (coe v9)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                     _ -> MAlonzo.RTE.mazUnreachableError))
                        MAlonzo.Code.Untyped.C_case_40 v6 v7
                          -> coe
                               seq (coe v5)
                               (let v8
                                      = coe
                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__76
                                          (coe d_isAllForced'63'_84 (coe v0) (coe v1) (coe v6))
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.du_all'63'_506
                                             (coe d_isAllForced'63'_84 (coe v0) (coe v1))
                                             (coe v7)) in
                                coe
                                  (case coe v8 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                       -> if coe v9
                                            then case coe v10 of
                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v11
                                                     -> case coe v11 of
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                            -> coe
                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                 (coe v9)
                                                                 (coe
                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                    (coe C_case_70 v12 v13))
                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            else coe
                                                   seq (coe v10)
                                                   (coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                      (coe v9)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                     _ -> MAlonzo.RTE.mazUnreachableError))
                        MAlonzo.Code.Untyped.C_builtin_44 v6
                          -> coe
                               seq (coe v5)
                               (coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                                  (coe
                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                     (coe C_builtin_56)))
                        MAlonzo.Code.Untyped.C_error_46
                          -> coe
                               seq (coe v5)
                               (coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                                  (coe
                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                     (coe C_error_50)))
                        _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.UFloatDelay..extendedlambda0
d_'46'extendedlambda0_136 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (T_AllForced_16 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isVar_14 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_AllForced_16 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda0_136 = erased
-- VerifiedCompilation.UFloatDelay..extendedlambda1
d_'46'extendedlambda1_180 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isForce_268 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_AllForced_16 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda1_180 = erased
-- VerifiedCompilation.UFloatDelay..extendedlambda2
d_'46'extendedlambda2_224 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (T_AllForced_16 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isForce_268 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_AllForced_16 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda2_224 = erased
-- VerifiedCompilation.UFloatDelay..extendedlambda3
d_'46'extendedlambda3_262 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isForce_268 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_AllForced_16 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda3_262 = erased
-- VerifiedCompilation.UFloatDelay..extendedlambda4
d_'46'extendedlambda4_274 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isForce_268 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  T_AllForced_16 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda4_274 = erased
-- VerifiedCompilation.UFloatDelay..extendedlambda5
d_'46'extendedlambda5_304 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (T_AllForced_16 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isForce_268 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_AllForced_16 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda5_304 = erased
-- VerifiedCompilation.UFloatDelay..extendedlambda6
d_'46'extendedlambda6_346 ::
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  Integer ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isForce_268 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_AllForced_16 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda6_346 = erased
-- VerifiedCompilation.UFloatDelay..extendedlambda7
d_'46'extendedlambda7_384 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isForce_268 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_AllForced_16 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda7_384 = erased
-- VerifiedCompilation.UFloatDelay.subs-delay
d_subs'45'delay_404 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14
d_subs'45'delay_404 ~v0 v1 v2 = du_subs'45'delay_404 v1 v2
du_subs'45'delay_404 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14
du_subs'45'delay_404 v0 v1
  = case coe v1 of
      MAlonzo.Code.Untyped.C_'96'_18 v2
        -> let v3
                 = coe
                     MAlonzo.Code.Data.Fin.Properties.du__'8799'__50 (coe v0)
                     (coe v2) in
           coe
             (case coe v3 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                  -> if coe v4
                       then coe
                              seq (coe v5)
                              (coe
                                 MAlonzo.Code.Untyped.C_delay_26
                                 (coe MAlonzo.Code.Untyped.C_'96'_18 (coe v0)))
                       else coe seq (coe v5) (coe v1)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Untyped.C_ƛ_20 v2
        -> coe
             MAlonzo.Code.Untyped.C_ƛ_20
             (coe
                du_subs'45'delay_404 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v0)
                (coe v2))
      MAlonzo.Code.Untyped.C__'183'__22 v2 v3
        -> coe
             MAlonzo.Code.Untyped.C__'183'__22
             (coe du_subs'45'delay_404 (coe v0) (coe v2))
             (coe du_subs'45'delay_404 (coe v0) (coe v3))
      MAlonzo.Code.Untyped.C_force_24 v2
        -> coe
             MAlonzo.Code.Untyped.C_force_24
             (coe du_subs'45'delay_404 (coe v0) (coe v2))
      MAlonzo.Code.Untyped.C_delay_26 v2
        -> coe
             MAlonzo.Code.Untyped.C_delay_26
             (coe du_subs'45'delay_404 (coe v0) (coe v2))
      MAlonzo.Code.Untyped.C_con_28 v2 -> coe v1
      MAlonzo.Code.Untyped.C_constr_34 v2 v3
        -> coe
             MAlonzo.Code.Untyped.C_constr_34 (coe v2)
             (coe
                MAlonzo.Code.Data.List.Base.du_map_22
                (coe du_subs'45'delay_404 (coe v0)) (coe v3))
      MAlonzo.Code.Untyped.C_case_40 v2 v3
        -> coe
             MAlonzo.Code.Untyped.C_case_40
             (coe du_subs'45'delay_404 (coe v0) (coe v2))
             (coe
                MAlonzo.Code.Data.List.Base.du_map_22
                (coe du_subs'45'delay_404 (coe v0)) (coe v3))
      MAlonzo.Code.Untyped.C_builtin_44 v2 -> coe v1
      MAlonzo.Code.Untyped.C_error_46 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.UFloatDelay.FlD
d_FlD_464 a0 a1 a2 = ()
data T_FlD_464
  = C_floatdelay_476 MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_12
                     MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_12
                     MAlonzo.Code.Untyped.Purity.T_Pure_6
-- VerifiedCompilation.UFloatDelay.FloatDelay
d_FloatDelay_484 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> ()
d_FloatDelay_484 = erased
-- VerifiedCompilation.UFloatDelay.isFloatDelay?
d_isFloatDelay'63'_488 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_86
d_isFloatDelay'63'_488 v0
  = coe
      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.du_translation'63'_164
      (coe v0)
      (coe MAlonzo.Code.VerifiedCompilation.Certificate.C_floatDelayT_6)
      (coe d_isFlD'63'_492)
-- VerifiedCompilation.UFloatDelay.isFlD?
d_isFlD'63'_492 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_86
d_isFlD'63'_492 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isApp'63'_166
              (coe v0)
              (coe
                 (\ v3 ->
                    coe
                      MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isLambda'63'_70
                      (coe v3)
                      (\ v4 v5 ->
                         coe
                           MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)))
              (coe
                 (\ v3 ->
                    coe
                      MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isDelay'63'_370
                      (coe v3)
                      (\ v4 v5 ->
                         coe
                           MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)))
              (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then case coe v5 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v6
                         -> case coe v6 of
                              MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isapp_154 v9 v10
                                -> case coe v1 of
                                     MAlonzo.Code.Untyped.C__'183'__22 v11 v12
                                       -> case coe v9 of
                                            MAlonzo.Code.VerifiedCompilation.UntypedViews.C_islambda_62 v14
                                              -> case coe v11 of
                                                   MAlonzo.Code.Untyped.C_ƛ_20 v15
                                                     -> coe
                                                          seq (coe v14)
                                                          (case coe v10 of
                                                             MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isdelay_362 v17
                                                               -> case coe v12 of
                                                                    MAlonzo.Code.Untyped.C_delay_26 v18
                                                                      -> coe
                                                                           seq (coe v17)
                                                                           (let v19
                                                                                  = coe
                                                                                      MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isApp'63'_166
                                                                                      (coe v0)
                                                                                      (coe
                                                                                         (\ v19 ->
                                                                                            coe
                                                                                              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isLambda'63'_70
                                                                                              (coe
                                                                                                 v19)
                                                                                              (\ v20
                                                                                                 v21 ->
                                                                                                 coe
                                                                                                   MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)))
                                                                                      (\ v19 v20 ->
                                                                                         coe
                                                                                           MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)
                                                                                      (coe v2) in
                                                                            coe
                                                                              (case coe v19 of
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                                                   -> if coe v20
                                                                                        then case coe
                                                                                                    v21 of
                                                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v22
                                                                                                 -> case coe
                                                                                                           v22 of
                                                                                                      MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isapp_154 v25 v26
                                                                                                        -> case coe
                                                                                                                  v2 of
                                                                                                             MAlonzo.Code.Untyped.C__'183'__22 v27 v28
                                                                                                               -> case coe
                                                                                                                         v25 of
                                                                                                                    MAlonzo.Code.VerifiedCompilation.UntypedViews.C_islambda_62 v30
                                                                                                                      -> case coe
                                                                                                                                v27 of
                                                                                                                           MAlonzo.Code.Untyped.C_ƛ_20 v31
                                                                                                                             -> coe
                                                                                                                                  seq
                                                                                                                                  (coe
                                                                                                                                     v30)
                                                                                                                                  (coe
                                                                                                                                     seq
                                                                                                                                     (coe
                                                                                                                                        v26)
                                                                                                                                     (let v32
                                                                                                                                            = coe
                                                                                                                                                d_isFloatDelay'63'_488
                                                                                                                                                (addInt
                                                                                                                                                   (coe
                                                                                                                                                      (1 ::
                                                                                                                                                         Integer))
                                                                                                                                                   (coe
                                                                                                                                                      v0))
                                                                                                                                                (coe
                                                                                                                                                   du_subs'45'delay_404
                                                                                                                                                   (coe
                                                                                                                                                      MAlonzo.Code.Data.Fin.Base.C_zero_12)
                                                                                                                                                   (coe
                                                                                                                                                      v15))
                                                                                                                                                v31 in
                                                                                                                                      coe
                                                                                                                                        (case coe
                                                                                                                                                v32 of
                                                                                                                                           MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_92 v33
                                                                                                                                             -> let v34
                                                                                                                                                      = coe
                                                                                                                                                          d_isFloatDelay'63'_488
                                                                                                                                                          v0
                                                                                                                                                          v18
                                                                                                                                                          v28 in
                                                                                                                                                coe
                                                                                                                                                  (case coe
                                                                                                                                                          v34 of
                                                                                                                                                     MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_92 v35
                                                                                                                                                       -> let v36
                                                                                                                                                                = MAlonzo.Code.Untyped.Purity.d_isPure'63'_72
                                                                                                                                                                    (coe
                                                                                                                                                                       v0)
                                                                                                                                                                    (coe
                                                                                                                                                                       v28) in
                                                                                                                                                          coe
                                                                                                                                                            (case coe
                                                                                                                                                                    v36 of
                                                                                                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v37 v38
                                                                                                                                                                 -> if coe
                                                                                                                                                                         v37
                                                                                                                                                                      then case coe
                                                                                                                                                                                  v38 of
                                                                                                                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v39
                                                                                                                                                                               -> coe
                                                                                                                                                                                    MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_92
                                                                                                                                                                                    (coe
                                                                                                                                                                                       C_floatdelay_476
                                                                                                                                                                                       v33
                                                                                                                                                                                       v35
                                                                                                                                                                                       v39)
                                                                                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                      else coe
                                                                                                                                                                             seq
                                                                                                                                                                             (coe
                                                                                                                                                                                v38)
                                                                                                                                                                             (coe
                                                                                                                                                                                MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_100
                                                                                                                                                                                (coe
                                                                                                                                                                                   MAlonzo.Code.VerifiedCompilation.Certificate.C_floatDelayT_6)
                                                                                                                                                                                v1
                                                                                                                                                                                v2)
                                                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                                     MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_100 v38 v39 v40
                                                                                                                                                       -> coe
                                                                                                                                                            MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_100
                                                                                                                                                            v38
                                                                                                                                                            v39
                                                                                                                                                            v40
                                                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                           MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_100 v36 v37 v38
                                                                                                                                             -> coe
                                                                                                                                                  MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_100
                                                                                                                                                  v36
                                                                                                                                                  v37
                                                                                                                                                  v38
                                                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError)))
                                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                        else coe
                                                                                               seq
                                                                                               (coe
                                                                                                  v21)
                                                                                               (coe
                                                                                                  MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_100
                                                                                                  (coe
                                                                                                     MAlonzo.Code.VerifiedCompilation.Certificate.C_floatDelayT_6)
                                                                                                  v1
                                                                                                  v2)
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError))
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v5)
                       (coe
                          MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_100
                          (coe MAlonzo.Code.VerifiedCompilation.Certificate.C_floatDelayT_6)
                          v1 v2)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.UFloatDelay..extendedlambda8
d_'46'extendedlambda8_508 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isApp_142 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  T_FlD_464 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda8_508 = erased
-- VerifiedCompilation.UFloatDelay..extendedlambda9
d_'46'extendedlambda9_538 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isApp_142 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  T_FlD_464 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda9_538 = erased
-- VerifiedCompilation.UFloatDelay..extendedlambda10
d_'46'extendedlambda10_582 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  T_FlD_464 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda10_582 = erased
-- VerifiedCompilation.UFloatDelay..extendedlambda11
d_'46'extendedlambda11_630 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_12 ->
  T_FlD_464 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda11_630 = erased
-- VerifiedCompilation.UFloatDelay..extendedlambda12
d_'46'extendedlambda12_676 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.Untyped.Purity.T_Pure_6 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_12 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_12 ->
  T_FlD_464 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda12_676 = erased
