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
import qualified MAlonzo.Code.VerifiedCompilation.UntypedTranslation
import qualified MAlonzo.Code.VerifiedCompilation.UntypedViews

-- VerifiedCompilation.UCaseOfCase.CoC
d_CoC_4 a0 a1 a2 a3 = ()
data T_CoC_4
  = C_isCoC_28 MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
               MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
               MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
-- VerifiedCompilation.UCaseOfCase.CaseOfCase
d_CaseOfCase_38 ::
  () ->
  MAlonzo.Code.Untyped.Equality.T_DecEq_6 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> ()
d_CaseOfCase_38 = erased
-- VerifiedCompilation.UCaseOfCase.CoCCase
d_CoCCase_42 a0 a1 = ()
data T_CoCCase_42 = C_isCoCCase_58
-- VerifiedCompilation.UCaseOfCase.isCoCCase?
d_isCoCCase'63'_62 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_isCoCCase'63'_62 ~v0 v1 = du_isCoCCase'63'_62 v1
du_isCoCCase'63'_62 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_isCoCCase'63'_62 v0
  = let v1
          = coe
              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isCase'63'_598
              erased
              (coe
                 (\ v1 ->
                    coe
                      MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isApp'63'_166
                      erased
                      (coe
                         (\ v2 ->
                            coe
                              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isApp'63'_166
                              erased
                              (coe
                                 (\ v3 ->
                                    coe
                                      MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isApp'63'_166
                                      erased
                                      (coe
                                         (\ v4 ->
                                            coe
                                              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isForce'63'_284
                                              erased
                                              (\ v5 v6 ->
                                                 coe
                                                   MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isBuiltin'63'_708
                                                   v6)))
                                      (\ v4 v5 ->
                                         coe
                                           MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)))
                              (coe
                                 (\ v3 ->
                                    coe
                                      MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isConstr'63'_496
                                      erased
                                      (\ v4 v5 ->
                                         coe
                                           MAlonzo.Code.VerifiedCompilation.UntypedViews.du_allTerms'63'_798)))))
                      (coe
                         (\ v2 ->
                            coe
                              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isConstr'63'_496
                              erased
                              (\ v3 v4 ->
                                 coe
                                   MAlonzo.Code.VerifiedCompilation.UntypedViews.du_allTerms'63'_798)))))
              (\ v1 v2 ->
                 coe
                   MAlonzo.Code.VerifiedCompilation.UntypedViews.du_allTerms'63'_798)
              (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
           -> if coe v2
                then case coe v3 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v4
                         -> case coe v4 of
                              MAlonzo.Code.VerifiedCompilation.UntypedViews.C_iscase_586 v7 v8
                                -> case coe v0 of
                                     MAlonzo.Code.Untyped.C_case_40 v9 v10
                                       -> case coe v7 of
                                            MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isapp_154 v13 v14
                                              -> case coe v9 of
                                                   MAlonzo.Code.Untyped.C__'183'__22 v15 v16
                                                     -> case coe v13 of
                                                          MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isapp_154 v19 v20
                                                            -> case coe v15 of
                                                                 MAlonzo.Code.Untyped.C__'183'__22 v21 v22
                                                                   -> case coe v19 of
                                                                        MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isapp_154 v25 v26
                                                                          -> case coe v21 of
                                                                               MAlonzo.Code.Untyped.C__'183'__22 v27 v28
                                                                                 -> case coe v25 of
                                                                                      MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isforce_276 v30
                                                                                        -> case coe
                                                                                                  v27 of
                                                                                             MAlonzo.Code.Untyped.C_force_24 v31
                                                                                               -> coe
                                                                                                    seq
                                                                                                    (coe
                                                                                                       v30)
                                                                                                    (case coe
                                                                                                            v31 of
                                                                                                       MAlonzo.Code.Untyped.C_builtin_44 v32
                                                                                                         -> coe
                                                                                                              seq
                                                                                                              (coe
                                                                                                                 v26)
                                                                                                              (case coe
                                                                                                                      v20 of
                                                                                                                 MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isconstr_488 v35
                                                                                                                   -> coe
                                                                                                                        seq
                                                                                                                        (coe
                                                                                                                           v35)
                                                                                                                        (case coe
                                                                                                                                v14 of
                                                                                                                           MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isconstr_488 v38
                                                                                                                             -> coe
                                                                                                                                  seq
                                                                                                                                  (coe
                                                                                                                                     v38)
                                                                                                                                  (coe
                                                                                                                                     seq
                                                                                                                                     (coe
                                                                                                                                        v8)
                                                                                                                                     (let v39
                                                                                                                                            = MAlonzo.Code.Builtin.d_decBuiltin_426
                                                                                                                                                (coe
                                                                                                                                                   v32)
                                                                                                                                                (coe
                                                                                                                                                   MAlonzo.Code.Builtin.C_ifThenElse_60) in
                                                                                                                                      coe
                                                                                                                                        (case coe
                                                                                                                                                v39 of
                                                                                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v40 v41
                                                                                                                                             -> if coe
                                                                                                                                                     v40
                                                                                                                                                  then coe
                                                                                                                                                         seq
                                                                                                                                                         (coe
                                                                                                                                                            v41)
                                                                                                                                                         (coe
                                                                                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                                                            (coe
                                                                                                                                                               v40)
                                                                                                                                                            (coe
                                                                                                                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                                                                               (coe
                                                                                                                                                                  C_isCoCCase_58)))
                                                                                                                                                  else coe
                                                                                                                                                         seq
                                                                                                                                                         (coe
                                                                                                                                                            v41)
                                                                                                                                                         (coe
                                                                                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                                                            (coe
                                                                                                                                                               v40)
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
                       seq (coe v3)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                          (coe v2)
                          (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.UCaseOfCase.CoCForce
d_CoCForce_146 a0 a1 = ()
data T_CoCForce_146 = C_isCoCForce_162
-- VerifiedCompilation.UCaseOfCase.isCoCForce?
d_isCoCForce'63'_168 ::
  () ->
  MAlonzo.Code.Untyped.Equality.T_DecEq_6 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_isCoCForce'63'_168 ~v0 v1 v2 = du_isCoCForce'63'_168 v1 v2
du_isCoCForce'63'_168 ::
  MAlonzo.Code.Untyped.Equality.T_DecEq_6 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_isCoCForce'63'_168 v0 v1
  = let v2
          = coe
              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isForce'63'_284
              erased
              (coe
                 (\ v2 ->
                    coe
                      MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isApp'63'_166
                      erased
                      (coe
                         (\ v3 ->
                            coe
                              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isApp'63'_166
                              erased
                              (coe
                                 (\ v4 ->
                                    coe
                                      MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isApp'63'_166
                                      erased
                                      (coe
                                         (\ v5 ->
                                            coe
                                              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isForce'63'_284
                                              erased
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
                                      erased
                                      (coe
                                         (\ v5 ->
                                            coe
                                              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isCase'63'_598
                                              erased
                                              (coe
                                                 (\ v6 ->
                                                    coe
                                                      MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isConstr'63'_496
                                                      erased
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
                              erased
                              (coe
                                 (\ v4 ->
                                    coe
                                      MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isCase'63'_598
                                      erased
                                      (coe
                                         (\ v5 ->
                                            coe
                                              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isConstr'63'_496
                                              erased
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
                                                                                                                                                                                                                 MAlonzo.Code.Untyped.Equality.du_DecEq'45'List_168
                                                                                                                                                                                                                 (coe
                                                                                                                                                                                                                    MAlonzo.Code.Untyped.Equality.du_DecEq'45''8866'_162
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
                                                                                                                                                                                                                                    C_isCoCForce_162)))
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
d_isCaseOfCase'63'_264 ::
  () ->
  MAlonzo.Code.Untyped.Equality.T_DecEq_6 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_28
d_isCaseOfCase'63'_264 ~v0 v1 = du_isCaseOfCase'63'_264 v1
du_isCaseOfCase'63'_264 ::
  MAlonzo.Code.Untyped.Equality.T_DecEq_6 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_28
du_isCaseOfCase'63'_264 v0
  = coe
      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.du_translation'63'_178
      erased (coe v0)
      (coe MAlonzo.Code.VerifiedCompilation.Certificate.C_caseOfCaseT_12)
      (\ v1 v2 v3 v4 -> coe du_isCoC'63'_274 v2 v3 v4)
-- VerifiedCompilation.UCaseOfCase.isCoC?
d_isCoC'63'_274 ::
  () ->
  MAlonzo.Code.Untyped.Equality.T_DecEq_6 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_28
d_isCoC'63'_274 ~v0 v1 v2 v3 = du_isCoC'63'_274 v1 v2 v3
du_isCoC'63'_274 ::
  MAlonzo.Code.Untyped.Equality.T_DecEq_6 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_28
du_isCoC'63'_274 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__76
              (coe du_isCoCCase'63'_62 (coe v1))
              (coe du_isCoCForce'63'_168 (coe v0) (coe v2)) in
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
                                                                                                                                                                      (coe
                                                                                                                                                                         MAlonzo.Code.Untyped.Equality.du_DecEq'45''8866'_162
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
                                                                                                                                                                                                     MAlonzo.Code.VerifiedCompilation.Certificate.du_pcePointwise_142
                                                                                                                                                                                                     (coe
                                                                                                                                                                                                        MAlonzo.Code.VerifiedCompilation.Certificate.C_caseOfCaseT_12)
                                                                                                                                                                                                     (coe
                                                                                                                                                                                                        du_isCaseOfCase'63'_264
                                                                                                                                                                                                        (coe
                                                                                                                                                                                                           v0))
                                                                                                                                                                                                     (coe
                                                                                                                                                                                                        v18)
                                                                                                                                                                                                     (coe
                                                                                                                                                                                                        v32) in
                                                                                                                                                                                           coe
                                                                                                                                                                                             (case coe
                                                                                                                                                                                                     v44 of
                                                                                                                                                                                                MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_34 v45
                                                                                                                                                                                                  -> let v46
                                                                                                                                                                                                           = coe
                                                                                                                                                                                                               MAlonzo.Code.VerifiedCompilation.Certificate.du_pcePointwise_142
                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                  MAlonzo.Code.VerifiedCompilation.Certificate.C_caseOfCaseT_12)
                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                  du_isCaseOfCase'63'_264
                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                     v0))
                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                  v20)
                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                  v37) in
                                                                                                                                                                                                     coe
                                                                                                                                                                                                       (case coe
                                                                                                                                                                                                               v46 of
                                                                                                                                                                                                          MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_34 v47
                                                                                                                                                                                                            -> let v48
                                                                                                                                                                                                                     = coe
                                                                                                                                                                                                                         MAlonzo.Code.VerifiedCompilation.Certificate.du_pcePointwise_142
                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                            MAlonzo.Code.VerifiedCompilation.Certificate.C_caseOfCaseT_12)
                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                            du_isCaseOfCase'63'_264
                                                                                                                                                                                                                            (coe
                                                                                                                                                                                                                               v0))
                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                            v10)
                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                            v30) in
                                                                                                                                                                                                               coe
                                                                                                                                                                                                                 (case coe
                                                                                                                                                                                                                         v48 of
                                                                                                                                                                                                                    MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_34 v49
                                                                                                                                                                                                                      -> coe
                                                                                                                                                                                                                           MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_34
                                                                                                                                                                                                                           (coe
                                                                                                                                                                                                                              C_isCoC_28
                                                                                                                                                                                                                              v49
                                                                                                                                                                                                                              v45
                                                                                                                                                                                                                              v47)
                                                                                                                                                                                                                    MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_42 v52 v53 v54
                                                                                                                                                                                                                      -> coe
                                                                                                                                                                                                                           MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_42
                                                                                                                                                                                                                           v52
                                                                                                                                                                                                                           v53
                                                                                                                                                                                                                           v54
                                                                                                                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                                                                                          MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_42 v50 v51 v52
                                                                                                                                                                                                            -> coe
                                                                                                                                                                                                                 MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_42
                                                                                                                                                                                                                 v50
                                                                                                                                                                                                                 v51
                                                                                                                                                                                                                 v52
                                                                                                                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                                                                                MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_42 v48 v49 v50
                                                                                                                                                                                                  -> coe
                                                                                                                                                                                                       MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_42
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
                                                                                                                                                                               MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_42
                                                                                                                                                                               (coe
                                                                                                                                                                                  MAlonzo.Code.VerifiedCompilation.Certificate.C_caseOfCaseT_12)
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
                          MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_42
                          (coe MAlonzo.Code.VerifiedCompilation.Certificate.C_caseOfCaseT_12)
                          v1 v2)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.UCaseOfCase..extendedlambda4
d_'46'extendedlambda4_290 ::
  () ->
  MAlonzo.Code.Untyped.Equality.T_DecEq_6 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_CoC_4 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda4_290 = erased
-- VerifiedCompilation.UCaseOfCase..extendedlambda5
d_'46'extendedlambda5_378 ::
  () ->
  MAlonzo.Code.Untyped.Equality.T_DecEq_6 ->
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
d_'46'extendedlambda5_378 = erased
-- VerifiedCompilation.UCaseOfCase..extendedlambda6
d_'46'extendedlambda6_454 ::
  () ->
  MAlonzo.Code.Untyped.Equality.T_DecEq_6 ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  (MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4 ->
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
d_'46'extendedlambda6_454 = erased
-- VerifiedCompilation.UCaseOfCase..extendedlambda7
d_'46'extendedlambda7_534 ::
  () ->
  MAlonzo.Code.Untyped.Equality.T_DecEq_6 ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  (MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4 ->
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
d_'46'extendedlambda7_534 = erased
-- VerifiedCompilation.UCaseOfCase..extendedlambda8
d_'46'extendedlambda8_618 ::
  () ->
  MAlonzo.Code.Untyped.Equality.T_DecEq_6 ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  (MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4 ->
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
d_'46'extendedlambda8_618 = erased
