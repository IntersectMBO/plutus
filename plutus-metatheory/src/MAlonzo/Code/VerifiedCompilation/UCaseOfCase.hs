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

module MAlonzo.Code.VerifiedCompilation.UCaseOfCase where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Builtin
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects
import qualified MAlonzo.Code.Untyped
import qualified MAlonzo.Code.Untyped.Equality
import qualified MAlonzo.Code.VerifiedCompilation.Certificate
import qualified MAlonzo.Code.VerifiedCompilation.Trace
import qualified MAlonzo.Code.VerifiedCompilation.UntypedTranslation
import qualified MAlonzo.Code.VerifiedCompilation.UntypedViews

-- VerifiedCompilation.UCaseOfCase.CoC
d_CoC_4 a0 a1 a2 = ()
data T_CoC_4
  = C_isCoC_26 MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
               MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
               MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
-- VerifiedCompilation.UCaseOfCase.CaseOfCase
d_CaseOfCase_34 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> ()
d_CaseOfCase_34 = erased
-- VerifiedCompilation.UCaseOfCase.CoCCase
d_CoCCase_38 a0 a1 = ()
data T_CoCCase_38 = C_isCoCCase_54
-- VerifiedCompilation.UCaseOfCase.isCoCCase?
d_isCoCCase'63'_58 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_isCoCCase'63'_58 v0 v1
  = let v2
          = coe
              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isCase'63'_598
              (coe v0)
              (coe
                 (\ v2 ->
                    coe
                      MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isApp'63'_166
                      (coe v2)
                      (coe
                         (\ v3 ->
                            coe
                              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isApp'63'_166
                              (coe v3)
                              (coe
                                 (\ v4 ->
                                    coe
                                      MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isApp'63'_166
                                      (coe v4)
                                      (coe
                                         (\ v5 ->
                                            coe
                                              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isForce'63'_284
                                              (coe v5)
                                              (\ v6 v7 ->
                                                 coe
                                                   MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isBuiltin'63'_708
                                                   v7)))
                                      (\ v5 v6 ->
                                         coe
                                           MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)))
                              (coe
                                 (\ v4 ->
                                    coe
                                      MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isConstr'63'_496
                                      (coe v4)
                                      (\ v5 v6 ->
                                         coe
                                           MAlonzo.Code.VerifiedCompilation.UntypedViews.du_allTerms'63'_798)))))
                      (coe
                         (\ v3 ->
                            coe
                              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isConstr'63'_496
                              (coe v3)
                              (\ v4 v5 ->
                                 coe
                                   MAlonzo.Code.VerifiedCompilation.UntypedViews.du_allTerms'63'_798)))))
              (\ v2 v3 ->
                 coe
                   MAlonzo.Code.VerifiedCompilation.UntypedViews.du_allTerms'63'_798)
              (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then case coe v4 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v5
                         -> case coe v5 of
                              MAlonzo.Code.VerifiedCompilation.UntypedViews.C_iscase_586 v8 v9
                                -> case coe v1 of
                                     MAlonzo.Code.Untyped.C_case_40 v10 v11
                                       -> case coe v8 of
                                            MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isapp_154 v14 v15
                                              -> case coe v10 of
                                                   MAlonzo.Code.Untyped.C__'183'__22 v16 v17
                                                     -> case coe v14 of
                                                          MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isapp_154 v20 v21
                                                            -> case coe v16 of
                                                                 MAlonzo.Code.Untyped.C__'183'__22 v22 v23
                                                                   -> case coe v20 of
                                                                        MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isapp_154 v26 v27
                                                                          -> case coe v22 of
                                                                               MAlonzo.Code.Untyped.C__'183'__22 v28 v29
                                                                                 -> case coe v26 of
                                                                                      MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isforce_276 v31
                                                                                        -> case coe
                                                                                                  v28 of
                                                                                             MAlonzo.Code.Untyped.C_force_24 v32
                                                                                               -> coe
                                                                                                    seq
                                                                                                    (coe
                                                                                                       v31)
                                                                                                    (case coe
                                                                                                            v32 of
                                                                                                       MAlonzo.Code.Untyped.C_builtin_44 v33
                                                                                                         -> coe
                                                                                                              seq
                                                                                                              (coe
                                                                                                                 v27)
                                                                                                              (case coe
                                                                                                                      v21 of
                                                                                                                 MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isconstr_488 v36
                                                                                                                   -> coe
                                                                                                                        seq
                                                                                                                        (coe
                                                                                                                           v36)
                                                                                                                        (case coe
                                                                                                                                v15 of
                                                                                                                           MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isconstr_488 v39
                                                                                                                             -> coe
                                                                                                                                  seq
                                                                                                                                  (coe
                                                                                                                                     v39)
                                                                                                                                  (coe
                                                                                                                                     seq
                                                                                                                                     (coe
                                                                                                                                        v9)
                                                                                                                                     (let v40
                                                                                                                                            = MAlonzo.Code.Builtin.d_decBuiltin_426
                                                                                                                                                (coe
                                                                                                                                                   v33)
                                                                                                                                                (coe
                                                                                                                                                   MAlonzo.Code.Builtin.C_ifThenElse_60) in
                                                                                                                                      coe
                                                                                                                                        (case coe
                                                                                                                                                v40 of
                                                                                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v41 v42
                                                                                                                                             -> if coe
                                                                                                                                                     v41
                                                                                                                                                  then coe
                                                                                                                                                         seq
                                                                                                                                                         (coe
                                                                                                                                                            v42)
                                                                                                                                                         (coe
                                                                                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                                                            (coe
                                                                                                                                                               v41)
                                                                                                                                                            (coe
                                                                                                                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                                                                               (coe
                                                                                                                                                                  C_isCoCCase_54)))
                                                                                                                                                  else coe
                                                                                                                                                         seq
                                                                                                                                                         (coe
                                                                                                                                                            v42)
                                                                                                                                                         (coe
                                                                                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                                                            (coe
                                                                                                                                                               v41)
                                                                                                                                                            (coe
                                                                                                                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError)))
                                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
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
                       seq (coe v4)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                          (coe v3)
                          (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.UCaseOfCase.CoCForce
d_CoCForce_142 a0 a1 = ()
data T_CoCForce_142 = C_isCoCForce_158
-- VerifiedCompilation.UCaseOfCase.isCoCForce?
d_isCoCForce'63'_162 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_isCoCForce'63'_162 v0 v1
  = let v2
          = coe
              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isForce'63'_284
              (coe v0)
              (coe
                 (\ v2 ->
                    coe
                      MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isApp'63'_166
                      (coe v2)
                      (coe
                         (\ v3 ->
                            coe
                              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isApp'63'_166
                              (coe v3)
                              (coe
                                 (\ v4 ->
                                    coe
                                      MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isApp'63'_166
                                      (coe v4)
                                      (coe
                                         (\ v5 ->
                                            coe
                                              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isForce'63'_284
                                              (coe v5)
                                              (\ v6 v7 ->
                                                 coe
                                                   MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isBuiltin'63'_708
                                                   v7)))
                                      (\ v5 v6 ->
                                         coe
                                           MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)))
                              (coe
                                 (\ v4 ->
                                    coe
                                      MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isDelay'63'_370
                                      (coe v4)
                                      (coe
                                         (\ v5 ->
                                            coe
                                              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isCase'63'_598
                                              (coe v5)
                                              (coe
                                                 (\ v6 ->
                                                    coe
                                                      MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isConstr'63'_496
                                                      (coe v6)
                                                      (\ v7 v8 ->
                                                         coe
                                                           MAlonzo.Code.VerifiedCompilation.UntypedViews.du_allTerms'63'_798)))
                                              (\ v6 v7 ->
                                                 coe
                                                   MAlonzo.Code.VerifiedCompilation.UntypedViews.du_allTerms'63'_798)))))))
                      (coe
                         (\ v3 ->
                            coe
                              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isDelay'63'_370
                              (coe v3)
                              (coe
                                 (\ v4 ->
                                    coe
                                      MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isCase'63'_598
                                      (coe v4)
                                      (coe
                                         (\ v5 ->
                                            coe
                                              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isConstr'63'_496
                                              (coe v5)
                                              (\ v6 v7 ->
                                                 coe
                                                   MAlonzo.Code.VerifiedCompilation.UntypedViews.du_allTerms'63'_798)))
                                      (\ v5 v6 ->
                                         coe
                                           MAlonzo.Code.VerifiedCompilation.UntypedViews.du_allTerms'63'_798)))))))
              (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then case coe v4 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v5
                         -> case coe v5 of
                              MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isforce_276 v7
                                -> case coe v1 of
                                     MAlonzo.Code.Untyped.C_force_24 v8
                                       -> case coe v7 of
                                            MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isapp_154 v11 v12
                                              -> case coe v8 of
                                                   MAlonzo.Code.Untyped.C__'183'__22 v13 v14
                                                     -> case coe v11 of
                                                          MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isapp_154 v17 v18
                                                            -> case coe v13 of
                                                                 MAlonzo.Code.Untyped.C__'183'__22 v19 v20
                                                                   -> case coe v17 of
                                                                        MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isapp_154 v23 v24
                                                                          -> case coe v19 of
                                                                               MAlonzo.Code.Untyped.C__'183'__22 v25 v26
                                                                                 -> case coe v23 of
                                                                                      MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isforce_276 v28
                                                                                        -> case coe
                                                                                                  v25 of
                                                                                             MAlonzo.Code.Untyped.C_force_24 v29
                                                                                               -> coe
                                                                                                    seq
                                                                                                    (coe
                                                                                                       v28)
                                                                                                    (case coe
                                                                                                            v29 of
                                                                                                       MAlonzo.Code.Untyped.C_builtin_44 v30
                                                                                                         -> coe
                                                                                                              seq
                                                                                                              (coe
                                                                                                                 v24)
                                                                                                              (case coe
                                                                                                                      v18 of
                                                                                                                 MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isdelay_362 v32
                                                                                                                   -> case coe
                                                                                                                             v20 of
                                                                                                                        MAlonzo.Code.Untyped.C_delay_26 v33
                                                                                                                          -> case coe
                                                                                                                                    v32 of
                                                                                                                               MAlonzo.Code.VerifiedCompilation.UntypedViews.C_iscase_586 v36 v37
                                                                                                                                 -> case coe
                                                                                                                                           v33 of
                                                                                                                                      MAlonzo.Code.Untyped.C_case_40 v38 v39
                                                                                                                                        -> case coe
                                                                                                                                                  v36 of
                                                                                                                                             MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isconstr_488 v42
                                                                                                                                               -> coe
                                                                                                                                                    seq
                                                                                                                                                    (coe
                                                                                                                                                       v42)
                                                                                                                                                    (coe
                                                                                                                                                       seq
                                                                                                                                                       (coe
                                                                                                                                                          v37)
                                                                                                                                                       (case coe
                                                                                                                                                               v12 of
                                                                                                                                                          MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isdelay_362 v44
                                                                                                                                                            -> case coe
                                                                                                                                                                      v14 of
                                                                                                                                                                 MAlonzo.Code.Untyped.C_delay_26 v45
                                                                                                                                                                   -> case coe
                                                                                                                                                                             v44 of
                                                                                                                                                                        MAlonzo.Code.VerifiedCompilation.UntypedViews.C_iscase_586 v48 v49
                                                                                                                                                                          -> case coe
                                                                                                                                                                                    v45 of
                                                                                                                                                                               MAlonzo.Code.Untyped.C_case_40 v50 v51
                                                                                                                                                                                 -> case coe
                                                                                                                                                                                           v48 of
                                                                                                                                                                                      MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isconstr_488 v54
                                                                                                                                                                                        -> coe
                                                                                                                                                                                             seq
                                                                                                                                                                                             (coe
                                                                                                                                                                                                v54)
                                                                                                                                                                                             (coe
                                                                                                                                                                                                seq
                                                                                                                                                                                                (coe
                                                                                                                                                                                                   v49)
                                                                                                                                                                                                (let v55
                                                                                                                                                                                                       = coe
                                                                                                                                                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__76
                                                                                                                                                                                                           (coe
                                                                                                                                                                                                              MAlonzo.Code.Builtin.d_decBuiltin_426
                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                 v30)
                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                 MAlonzo.Code.Builtin.C_ifThenElse_60))
                                                                                                                                                                                                           (coe
                                                                                                                                                                                                              MAlonzo.Code.Untyped.Equality.d__'8799'__12
                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                 MAlonzo.Code.Untyped.Equality.du_DecEq'45'List_152
                                                                                                                                                                                                                 (coe
                                                                                                                                                                                                                    MAlonzo.Code.Untyped.Equality.d_DecEq'45''8866'_146
                                                                                                                                                                                                                    (coe
                                                                                                                                                                                                                       v0)))
                                                                                                                                                                                                              v39
                                                                                                                                                                                                              v51) in
                                                                                                                                                                                                 coe
                                                                                                                                                                                                   (case coe
                                                                                                                                                                                                           v55 of
                                                                                                                                                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v56 v57
                                                                                                                                                                                                        -> if coe
                                                                                                                                                                                                                v56
                                                                                                                                                                                                             then case coe
                                                                                                                                                                                                                         v57 of
                                                                                                                                                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v58
                                                                                                                                                                                                                      -> coe
                                                                                                                                                                                                                           seq
                                                                                                                                                                                                                           (coe
                                                                                                                                                                                                                              v58)
                                                                                                                                                                                                                           (coe
                                                                                                                                                                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                 v56)
                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                                                                                                                                                 (coe
                                                                                                                                                                                                                                    C_isCoCForce_158)))
                                                                                                                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                             else coe
                                                                                                                                                                                                                    seq
                                                                                                                                                                                                                    (coe
                                                                                                                                                                                                                       v57)
                                                                                                                                                                                                                    (coe
                                                                                                                                                                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                                                                                                                       (coe
                                                                                                                                                                                                                          v56)
                                                                                                                                                                                                                       (coe
                                                                                                                                                                                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError)))
                                                                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
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
                       seq (coe v4)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                          (coe v3)
                          (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.UCaseOfCase.isCaseOfCase?
d_isCaseOfCase'63'_256 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_38
d_isCaseOfCase'63'_256 v0
  = coe
      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.du_translation'63'_164
      (coe v0)
      (coe MAlonzo.Code.VerifiedCompilation.Trace.C_caseOfCaseT_12)
      (coe d_isCoC'63'_264)
-- VerifiedCompilation.UCaseOfCase.isCoC?
d_isCoC'63'_264 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_38
d_isCoC'63'_264 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__76
              (coe d_isCoCCase'63'_58 (coe v0) (coe v1))
              (coe d_isCoCForce'63'_162 (coe v0) (coe v2)) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then case coe v5 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v6
                         -> case coe v6 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                -> coe
                                     seq (coe v7)
                                     (case coe v1 of
                                        MAlonzo.Code.Untyped.C_case_40 v9 v10
                                          -> case coe v9 of
                                               MAlonzo.Code.Untyped.C__'183'__22 v11 v12
                                                 -> case coe v11 of
                                                      MAlonzo.Code.Untyped.C__'183'__22 v13 v14
                                                        -> case coe v13 of
                                                             MAlonzo.Code.Untyped.C__'183'__22 v15 v16
                                                               -> case coe v14 of
                                                                    MAlonzo.Code.Untyped.C_constr_34 v17 v18
                                                                      -> case coe v12 of
                                                                           MAlonzo.Code.Untyped.C_constr_34 v19 v20
                                                                             -> coe
                                                                                  seq (coe v8)
                                                                                  (case coe v2 of
                                                                                     MAlonzo.Code.Untyped.C_force_24 v21
                                                                                       -> case coe
                                                                                                 v21 of
                                                                                            MAlonzo.Code.Untyped.C__'183'__22 v22 v23
                                                                                              -> case coe
                                                                                                        v22 of
                                                                                                   MAlonzo.Code.Untyped.C__'183'__22 v24 v25
                                                                                                     -> case coe
                                                                                                               v24 of
                                                                                                          MAlonzo.Code.Untyped.C__'183'__22 v26 v27
                                                                                                            -> case coe
                                                                                                                      v25 of
                                                                                                                 MAlonzo.Code.Untyped.C_delay_26 v28
                                                                                                                   -> case coe
                                                                                                                             v28 of
                                                                                                                        MAlonzo.Code.Untyped.C_case_40 v29 v30
                                                                                                                          -> case coe
                                                                                                                                    v29 of
                                                                                                                               MAlonzo.Code.Untyped.C_constr_34 v31 v32
                                                                                                                                 -> case coe
                                                                                                                                           v23 of
                                                                                                                                      MAlonzo.Code.Untyped.C_delay_26 v33
                                                                                                                                        -> case coe
                                                                                                                                                  v33 of
                                                                                                                                             MAlonzo.Code.Untyped.C_case_40 v34 v35
                                                                                                                                               -> case coe
                                                                                                                                                         v34 of
                                                                                                                                                    MAlonzo.Code.Untyped.C_constr_34 v36 v37
                                                                                                                                                      -> let v38
                                                                                                                                                               = coe
                                                                                                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__76
                                                                                                                                                                   (coe
                                                                                                                                                                      MAlonzo.Code.Untyped.Equality.d__'8799'__12
                                                                                                                                                                      (MAlonzo.Code.Untyped.Equality.d_DecEq'45''8866'_146
                                                                                                                                                                         (coe
                                                                                                                                                                            v0))
                                                                                                                                                                      v16
                                                                                                                                                                      v27)
                                                                                                                                                                   (coe
                                                                                                                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__76
                                                                                                                                                                      (coe
                                                                                                                                                                         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2688
                                                                                                                                                                         (coe
                                                                                                                                                                            v17)
                                                                                                                                                                         (coe
                                                                                                                                                                            v31))
                                                                                                                                                                      (coe
                                                                                                                                                                         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2688
                                                                                                                                                                         (coe
                                                                                                                                                                            v19)
                                                                                                                                                                         (coe
                                                                                                                                                                            v36))) in
                                                                                                                                                         coe
                                                                                                                                                           (case coe
                                                                                                                                                                   v38 of
                                                                                                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v39 v40
                                                                                                                                                                -> if coe
                                                                                                                                                                        v39
                                                                                                                                                                     then case coe
                                                                                                                                                                                 v40 of
                                                                                                                                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v41
                                                                                                                                                                              -> case coe
                                                                                                                                                                                        v41 of
                                                                                                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v42 v43
                                                                                                                                                                                     -> coe
                                                                                                                                                                                          seq
                                                                                                                                                                                          (coe
                                                                                                                                                                                             v43)
                                                                                                                                                                                          (let v44
                                                                                                                                                                                                 = coe
                                                                                                                                                                                                     MAlonzo.Code.VerifiedCompilation.Certificate.du_pcePointwise_286
                                                                                                                                                                                                     (coe
                                                                                                                                                                                                        MAlonzo.Code.VerifiedCompilation.Trace.C_caseOfCaseT_12)
                                                                                                                                                                                                     (coe
                                                                                                                                                                                                        d_isCaseOfCase'63'_256
                                                                                                                                                                                                        (coe
                                                                                                                                                                                                           v0))
                                                                                                                                                                                                     (coe
                                                                                                                                                                                                        v18)
                                                                                                                                                                                                     (coe
                                                                                                                                                                                                        v32) in
                                                                                                                                                                                           coe
                                                                                                                                                                                             (case coe
                                                                                                                                                                                                     v44 of
                                                                                                                                                                                                MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_44 v45
                                                                                                                                                                                                  -> let v46
                                                                                                                                                                                                           = coe
                                                                                                                                                                                                               MAlonzo.Code.VerifiedCompilation.Certificate.du_pcePointwise_286
                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                  MAlonzo.Code.VerifiedCompilation.Trace.C_caseOfCaseT_12)
                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                  d_isCaseOfCase'63'_256
                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                     v0))
                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                  v20)
                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                  v37) in
                                                                                                                                                                                                     coe
                                                                                                                                                                                                       (case coe
                                                                                                                                                                                                               v46 of
                                                                                                                                                                                                          MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_44 v47
                                                                                                                                                                                                            -> let v48
                                                                                                                                                                                                                     = coe
                                                                                                                                                                                                                         MAlonzo.Code.VerifiedCompilation.Certificate.du_pcePointwise_286
                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                            MAlonzo.Code.VerifiedCompilation.Trace.C_caseOfCaseT_12)
                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                            d_isCaseOfCase'63'_256
                                                                                                                                                                                                                            (coe
                                                                                                                                                                                                                               v0))
                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                            v10)
                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                            v30) in
                                                                                                                                                                                                               coe
                                                                                                                                                                                                                 (case coe
                                                                                                                                                                                                                         v48 of
                                                                                                                                                                                                                    MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_44 v49
                                                                                                                                                                                                                      -> coe
                                                                                                                                                                                                                           MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_44
                                                                                                                                                                                                                           (coe
                                                                                                                                                                                                                              C_isCoC_26
                                                                                                                                                                                                                              v49
                                                                                                                                                                                                                              v45
                                                                                                                                                                                                                              v47)
                                                                                                                                                                                                                    MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52 v52 v53 v54
                                                                                                                                                                                                                      -> coe
                                                                                                                                                                                                                           MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52
                                                                                                                                                                                                                           v52
                                                                                                                                                                                                                           v53
                                                                                                                                                                                                                           v54
                                                                                                                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                                                                                          MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52 v50 v51 v52
                                                                                                                                                                                                            -> coe
                                                                                                                                                                                                                 MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52
                                                                                                                                                                                                                 v50
                                                                                                                                                                                                                 v51
                                                                                                                                                                                                                 v52
                                                                                                                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                                                                                MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52 v48 v49 v50
                                                                                                                                                                                                  -> coe
                                                                                                                                                                                                       MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52
                                                                                                                                                                                                       v48
                                                                                                                                                                                                       v49
                                                                                                                                                                                                       v50
                                                                                                                                                                                                _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                     else coe
                                                                                                                                                                            seq
                                                                                                                                                                            (coe
                                                                                                                                                                               v40)
                                                                                                                                                                            (coe
                                                                                                                                                                               MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52
                                                                                                                                                                               (coe
                                                                                                                                                                                  MAlonzo.Code.VerifiedCompilation.Trace.C_caseOfCaseT_12)
                                                                                                                                                                               (coe
                                                                                                                                                                                  MAlonzo.Code.Untyped.C_case_40
                                                                                                                                                                                  (coe
                                                                                                                                                                                     MAlonzo.Code.Untyped.C__'183'__22
                                                                                                                                                                                     (coe
                                                                                                                                                                                        MAlonzo.Code.Untyped.C__'183'__22
                                                                                                                                                                                        (coe
                                                                                                                                                                                           MAlonzo.Code.Untyped.C__'183'__22
                                                                                                                                                                                           (coe
                                                                                                                                                                                              MAlonzo.Code.Untyped.C_force_24
                                                                                                                                                                                              (coe
                                                                                                                                                                                                 MAlonzo.Code.Untyped.C_builtin_44
                                                                                                                                                                                                 (coe
                                                                                                                                                                                                    MAlonzo.Code.Builtin.C_ifThenElse_60)))
                                                                                                                                                                                           (coe
                                                                                                                                                                                              v16))
                                                                                                                                                                                        (coe
                                                                                                                                                                                           v14))
                                                                                                                                                                                     (coe
                                                                                                                                                                                        v12))
                                                                                                                                                                                  (coe
                                                                                                                                                                                     v10))
                                                                                                                                                                               (coe
                                                                                                                                                                                  MAlonzo.Code.Untyped.C_force_24
                                                                                                                                                                                  (coe
                                                                                                                                                                                     MAlonzo.Code.Untyped.C__'183'__22
                                                                                                                                                                                     (coe
                                                                                                                                                                                        MAlonzo.Code.Untyped.C__'183'__22
                                                                                                                                                                                        (coe
                                                                                                                                                                                           MAlonzo.Code.Untyped.C__'183'__22
                                                                                                                                                                                           (coe
                                                                                                                                                                                              MAlonzo.Code.Untyped.C_force_24
                                                                                                                                                                                              (coe
                                                                                                                                                                                                 MAlonzo.Code.Untyped.C_builtin_44
                                                                                                                                                                                                 (coe
                                                                                                                                                                                                    MAlonzo.Code.Builtin.C_ifThenElse_60)))
                                                                                                                                                                                           (coe
                                                                                                                                                                                              v27))
                                                                                                                                                                                        (coe
                                                                                                                                                                                           v25))
                                                                                                                                                                                     (coe
                                                                                                                                                                                        MAlonzo.Code.Untyped.C_delay_26
                                                                                                                                                                                        (coe
                                                                                                                                                                                           MAlonzo.Code.Untyped.C_case_40
                                                                                                                                                                                           (coe
                                                                                                                                                                                              v34)
                                                                                                                                                                                           (coe
                                                                                                                                                                                              v30))))))
                                                                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v5)
                       (coe
                          MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52
                          (coe MAlonzo.Code.VerifiedCompilation.Trace.C_caseOfCaseT_12) v1
                          v2)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.UCaseOfCase..extendedlambda4
d_'46'extendedlambda4_280 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_CoC_4 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda4_280 = erased
-- VerifiedCompilation.UCaseOfCase..extendedlambda5
d_'46'extendedlambda5_368 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  T_CoC_4 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda5_368 = erased
-- VerifiedCompilation.UCaseOfCase..extendedlambda6
d_'46'extendedlambda6_444 ::
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  (MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Trace.T_SimplifierTag_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  T_CoC_4 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda6_444 = erased
-- VerifiedCompilation.UCaseOfCase..extendedlambda7
d_'46'extendedlambda7_524 ::
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  (MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Trace.T_SimplifierTag_4 ->
  AgdaAny ->
  AgdaAny ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  T_CoC_4 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda7_524 = erased
-- VerifiedCompilation.UCaseOfCase..extendedlambda8
d_'46'extendedlambda8_608 ::
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  (MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Trace.T_SimplifierTag_4 ->
  AgdaAny ->
  AgdaAny ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Integer ->
  Integer -> T_CoC_4 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda8_608 = erased
-- VerifiedCompilation.UCaseOfCase.certCaseOfCase
d_certCaseOfCase_652 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_CertResult_12
d_certCaseOfCase_652
  = coe
      MAlonzo.Code.VerifiedCompilation.Certificate.du_runDecider_174
      (coe d_isCaseOfCase'63'_256 (coe (0 :: Integer)))
