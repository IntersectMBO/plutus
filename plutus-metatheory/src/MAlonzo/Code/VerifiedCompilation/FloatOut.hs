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

module MAlonzo.Code.VerifiedCompilation.FloatOut where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects
import qualified MAlonzo.Code.Untyped
import qualified MAlonzo.Code.Untyped.Relation.Binary.Core
import qualified MAlonzo.Code.Untyped.Relation.Binary.Modular
import qualified MAlonzo.Code.Untyped.RenamingSubstitution
import qualified MAlonzo.Code.VerifiedCompilation.Certificate
import qualified MAlonzo.Code.VerifiedCompilation.Trace
import qualified MAlonzo.Code.VerifiedCompilation.UntypedViews

-- VerifiedCompilation.FloatOut.FloatApply
d_FloatApply_6 a0 a1 a2 a3 = ()
data T_FloatApply_6 = C_float'45'apply_22 AgdaAny AgdaAny
-- VerifiedCompilation.FloatOut.FloatCase
d_FloatCase_26 a0 a1 a2 a3 = ()
data T_FloatCase_26
  = C_float'45'case_42 AgdaAny
                       MAlonzo.Code.Untyped.Relation.Binary.Core.T_Pointwise_20
-- VerifiedCompilation.FloatOut.FloatForce
d_FloatForce_46 a0 a1 a2 a3 = ()
newtype T_FloatForce_46 = C_float'45'force_58 AgdaAny
-- VerifiedCompilation.FloatOut.FloatOut
d_FloatOut_60 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> ()
d_FloatOut_60 = erased
-- VerifiedCompilation.FloatOut.apply-dec
d_apply'45'dec_62 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_apply'45'dec_62 ~v0 v1 v2 v3 v4 = du_apply'45'dec_62 v1 v2 v3 v4
du_apply'45'dec_62 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_apply'45'dec_62 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
              (coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du__'183''63'__1260
                 (\ v4 ->
                    coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2404)
                 (\ v4 ->
                    coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2404)
                 (coe v2))
              (coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du_let'''63'_2390
                 (\ v4 ->
                    coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2404)
                 (coe
                    MAlonzo.Code.VerifiedCompilation.UntypedViews.du__'183''63'__1260
                    (\ v4 ->
                       coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2404)
                    (\ v4 ->
                       coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2404))
                 v3) in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v7
                         -> case coe v7 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                -> case coe v8 of
                                     MAlonzo.Code.VerifiedCompilation.UntypedViews.C__'183''33'__894 v12 v13
                                       -> case coe v2 of
                                            MAlonzo.Code.Untyped.C__'183'__22 v14 v15
                                              -> coe
                                                   seq (coe v12)
                                                   (coe
                                                      seq (coe v13)
                                                      (case coe v9 of
                                                         MAlonzo.Code.VerifiedCompilation.UntypedViews.C_Let'33'_In'33'__1042 v18 v19
                                                           -> case coe v3 of
                                                                MAlonzo.Code.Untyped.C__'183'__22 v20 v21
                                                                  -> case coe v20 of
                                                                       MAlonzo.Code.Untyped.C_ƛ_20 v22
                                                                         -> coe
                                                                              seq (coe v18)
                                                                              (case coe v19 of
                                                                                 MAlonzo.Code.VerifiedCompilation.UntypedViews.C__'183''33'__894 v25 v26
                                                                                   -> case coe
                                                                                             v22 of
                                                                                        MAlonzo.Code.Untyped.C__'183'__22 v27 v28
                                                                                          -> coe
                                                                                               seq
                                                                                               (coe
                                                                                                  v25)
                                                                                               (coe
                                                                                                  seq
                                                                                                  (coe
                                                                                                     v26)
                                                                                                  (let v29
                                                                                                         = coe
                                                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                                                                                                             (coe
                                                                                                                v0
                                                                                                                v1
                                                                                                                v14
                                                                                                                (coe
                                                                                                                   MAlonzo.Code.Untyped.C__'183'__22
                                                                                                                   (coe
                                                                                                                      MAlonzo.Code.Untyped.C_ƛ_20
                                                                                                                      (coe
                                                                                                                         v27))
                                                                                                                   (coe
                                                                                                                      v21)))
                                                                                                             (coe
                                                                                                                v0
                                                                                                                (addInt
                                                                                                                   (coe
                                                                                                                      (1 ::
                                                                                                                         Integer))
                                                                                                                   (coe
                                                                                                                      v1))
                                                                                                                (MAlonzo.Code.Untyped.RenamingSubstitution.d_weaken_88
                                                                                                                   (coe
                                                                                                                      v1)
                                                                                                                   (coe
                                                                                                                      v15))
                                                                                                                v28) in
                                                                                                   coe
                                                                                                     (case coe
                                                                                                             v29 of
                                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v30 v31
                                                                                                          -> if coe
                                                                                                                  v30
                                                                                                               then case coe
                                                                                                                           v31 of
                                                                                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v32
                                                                                                                        -> case coe
                                                                                                                                  v32 of
                                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v33 v34
                                                                                                                               -> coe
                                                                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                                    (coe
                                                                                                                                       v30)
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                                                       (coe
                                                                                                                                          C_float'45'apply_22
                                                                                                                                          v33
                                                                                                                                          v34))
                                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                               else coe
                                                                                                                      seq
                                                                                                                      (coe
                                                                                                                         v31)
                                                                                                                      (coe
                                                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                         (coe
                                                                                                                            v30)
                                                                                                                         (coe
                                                                                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError)))
                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         _ -> MAlonzo.RTE.mazUnreachableError))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v6)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                          (coe v5)
                          (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.FloatOut.case-dec
d_case'45'dec_148 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_case'45'dec_148 ~v0 v1 v2 v3 v4 = du_case'45'dec_148 v1 v2 v3 v4
du_case'45'dec_148 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_case'45'dec_148 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
              (coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du_case'63'_1532
                 (\ v4 ->
                    coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2404)
                 (\ v4 ->
                    coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2404)
                 (coe v2))
              (coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du_let'''63'_2390
                 (\ v4 ->
                    coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2404)
                 (coe
                    MAlonzo.Code.VerifiedCompilation.UntypedViews.du_case'63'_1532
                    (\ v4 ->
                       coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2404)
                    (\ v4 ->
                       coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2404))
                 v3) in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v7
                         -> case coe v7 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                -> case coe v8 of
                                     MAlonzo.Code.VerifiedCompilation.UntypedViews.C_case'33'_936 v12 v13
                                       -> case coe v2 of
                                            MAlonzo.Code.Untyped.C_case_40 v14 v15
                                              -> coe
                                                   seq (coe v12)
                                                   (coe
                                                      seq (coe v13)
                                                      (case coe v9 of
                                                         MAlonzo.Code.VerifiedCompilation.UntypedViews.C_Let'33'_In'33'__1042 v18 v19
                                                           -> case coe v3 of
                                                                MAlonzo.Code.Untyped.C__'183'__22 v20 v21
                                                                  -> case coe v20 of
                                                                       MAlonzo.Code.Untyped.C_ƛ_20 v22
                                                                         -> coe
                                                                              seq (coe v18)
                                                                              (case coe v19 of
                                                                                 MAlonzo.Code.VerifiedCompilation.UntypedViews.C_case'33'_936 v25 v26
                                                                                   -> case coe
                                                                                             v22 of
                                                                                        MAlonzo.Code.Untyped.C_case_40 v27 v28
                                                                                          -> coe
                                                                                               seq
                                                                                               (coe
                                                                                                  v25)
                                                                                               (coe
                                                                                                  seq
                                                                                                  (coe
                                                                                                     v26)
                                                                                                  (let v29
                                                                                                         = coe
                                                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                                                                                                             (coe
                                                                                                                v0
                                                                                                                v1
                                                                                                                v14
                                                                                                                (coe
                                                                                                                   MAlonzo.Code.Untyped.C__'183'__22
                                                                                                                   (coe
                                                                                                                      MAlonzo.Code.Untyped.C_ƛ_20
                                                                                                                      (coe
                                                                                                                         v27))
                                                                                                                   (coe
                                                                                                                      v21)))
                                                                                                             (coe
                                                                                                                MAlonzo.Code.Untyped.Relation.Binary.Core.du_pointwise'63'_56
                                                                                                                (coe
                                                                                                                   v0)
                                                                                                                (coe
                                                                                                                   addInt
                                                                                                                   (coe
                                                                                                                      (1 ::
                                                                                                                         Integer))
                                                                                                                   (coe
                                                                                                                      v1))
                                                                                                                (coe
                                                                                                                   MAlonzo.Code.Data.List.Base.du_map_22
                                                                                                                   (coe
                                                                                                                      MAlonzo.Code.Untyped.RenamingSubstitution.d_weaken_88
                                                                                                                      (coe
                                                                                                                         v1))
                                                                                                                   (coe
                                                                                                                      v15))
                                                                                                                (coe
                                                                                                                   v28)) in
                                                                                                   coe
                                                                                                     (case coe
                                                                                                             v29 of
                                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v30 v31
                                                                                                          -> if coe
                                                                                                                  v30
                                                                                                               then case coe
                                                                                                                           v31 of
                                                                                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v32
                                                                                                                        -> case coe
                                                                                                                                  v32 of
                                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v33 v34
                                                                                                                               -> coe
                                                                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                                    (coe
                                                                                                                                       v30)
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                                                       (coe
                                                                                                                                          C_float'45'case_42
                                                                                                                                          v33
                                                                                                                                          v34))
                                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                               else coe
                                                                                                                      seq
                                                                                                                      (coe
                                                                                                                         v31)
                                                                                                                      (coe
                                                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                         (coe
                                                                                                                            v30)
                                                                                                                         (coe
                                                                                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError)))
                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         _ -> MAlonzo.RTE.mazUnreachableError))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v6)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                          (coe v5)
                          (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.FloatOut.force-dec
d_force'45'dec_234 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_force'45'dec_234 ~v0 v1 v2 v3 v4
  = du_force'45'dec_234 v1 v2 v3 v4
du_force'45'dec_234 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_force'45'dec_234 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
              (coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du_force'63'_1374
                 (\ v4 ->
                    coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2404)
                 (coe v2))
              (coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du_let'''63'_2390
                 (\ v4 ->
                    coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2404)
                 (coe
                    MAlonzo.Code.VerifiedCompilation.UntypedViews.du_force'63'_1374
                    (\ v4 ->
                       coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2404))
                 v3) in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v7
                         -> case coe v7 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                -> case coe v8 of
                                     MAlonzo.Code.VerifiedCompilation.UntypedViews.C_force'33'_906 v11
                                       -> case coe v2 of
                                            MAlonzo.Code.Untyped.C_force_24 v12
                                              -> coe
                                                   seq (coe v11)
                                                   (case coe v9 of
                                                      MAlonzo.Code.VerifiedCompilation.UntypedViews.C_Let'33'_In'33'__1042 v15 v16
                                                        -> case coe v3 of
                                                             MAlonzo.Code.Untyped.C__'183'__22 v17 v18
                                                               -> case coe v17 of
                                                                    MAlonzo.Code.Untyped.C_ƛ_20 v19
                                                                      -> coe
                                                                           seq (coe v15)
                                                                           (case coe v16 of
                                                                              MAlonzo.Code.VerifiedCompilation.UntypedViews.C_force'33'_906 v21
                                                                                -> case coe v19 of
                                                                                     MAlonzo.Code.Untyped.C_force_24 v22
                                                                                       -> coe
                                                                                            seq
                                                                                            (coe
                                                                                               v21)
                                                                                            (let v23
                                                                                                   = coe
                                                                                                       v0
                                                                                                       v1
                                                                                                       v12
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Untyped.C__'183'__22
                                                                                                          (coe
                                                                                                             MAlonzo.Code.Untyped.C_ƛ_20
                                                                                                             (coe
                                                                                                                v22))
                                                                                                          (coe
                                                                                                             v18)) in
                                                                                             coe
                                                                                               (case coe
                                                                                                       v23 of
                                                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v24 v25
                                                                                                    -> if coe
                                                                                                            v24
                                                                                                         then case coe
                                                                                                                     v25 of
                                                                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v26
                                                                                                                  -> coe
                                                                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                       (coe
                                                                                                                          v24)
                                                                                                                       (coe
                                                                                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                                          (coe
                                                                                                                             C_float'45'force_58
                                                                                                                             v26))
                                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                         else coe
                                                                                                                seq
                                                                                                                (coe
                                                                                                                   v25)
                                                                                                                (coe
                                                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                   (coe
                                                                                                                      v24)
                                                                                                                   (coe
                                                                                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v6)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                          (coe v5)
                          (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.FloatOut.dec
d_dec_304 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_dec_304 v0
  = coe
      MAlonzo.Code.Untyped.Relation.Binary.Modular.du_Fix'45'dec_348
      (coe
         MAlonzo.Code.Untyped.Relation.Binary.Modular.du__'8853''45'dec__260
         (\ v1 ->
            coe
              MAlonzo.Code.Untyped.Relation.Binary.Modular.du_compatTerm'63'_1020)
         (coe
            MAlonzo.Code.Untyped.Relation.Binary.Modular.du__'8853''45'dec__260
            (\ v1 v2 v3 v4 v5 -> coe du_apply'45'dec_62 v2 v3 v4 v5)
            (coe
               MAlonzo.Code.Untyped.Relation.Binary.Modular.du__'8853''45'dec__260
               (\ v1 v2 v3 v4 v5 -> coe du_case'45'dec_148 v2 v3 v4 v5)
               (coe
                  MAlonzo.Code.Untyped.Relation.Binary.Modular.du__'8853''45'dec__260
                  (\ v1 v2 v3 v4 v5 -> coe du_force'45'dec_234 v2 v3 v4 v5)
                  (\ v1 v2 v3 v4 v5 ->
                     coe
                       MAlonzo.Code.Untyped.Relation.Binary.Modular.du_empty'63'_338)))))
      (coe v0)
-- VerifiedCompilation.FloatOut.decide
d_decide_312 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_50
d_decide_312 v0 v1 v2
  = let v3 = coe d_dec_304 v0 v1 v2 in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then case coe v5 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v6
                         -> coe
                              MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_56 (coe v6)
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v5)
                       (coe
                          MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_64
                          MAlonzo.Code.VerifiedCompilation.Trace.d_LetFloatOutT_44 v1 v2)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.FloatOut.numSites
d_numSites_330 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.Relation.Binary.Modular.T_Fix_50 -> Integer
d_numSites_330 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Untyped.Relation.Binary.Modular.C_fix_60 v7
        -> case coe v7 of
             MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inl_30 v11
               -> coe
                    d_numSites'45'compat_346 (coe v0) (coe v1) (coe v2) (coe v11)
             MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38 v11
               -> case coe v11 of
                    MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inl_30 v15
                      -> case coe v15 of
                           C_float'45'apply_22 v22 v23
                             -> case coe v1 of
                                  MAlonzo.Code.Untyped.C__'183'__22 v24 v25
                                    -> case coe v2 of
                                         MAlonzo.Code.Untyped.C__'183'__22 v26 v27
                                           -> case coe v26 of
                                                MAlonzo.Code.Untyped.C_ƛ_20 v28
                                                  -> case coe v28 of
                                                       MAlonzo.Code.Untyped.C__'183'__22 v29 v30
                                                         -> coe
                                                              addInt
                                                              (coe
                                                                 addInt (coe (1 :: Integer))
                                                                 (coe
                                                                    d_numSites_330
                                                                    (coe
                                                                       addInt (coe (1 :: Integer))
                                                                       (coe v0))
                                                                    (coe
                                                                       MAlonzo.Code.Untyped.RenamingSubstitution.d_weaken_88
                                                                       (coe v0) (coe v25))
                                                                    (coe v30) (coe v23)))
                                                              (coe
                                                                 d_numSites_330 (coe v0) (coe v24)
                                                                 (coe
                                                                    MAlonzo.Code.Untyped.C__'183'__22
                                                                    (coe
                                                                       MAlonzo.Code.Untyped.C_ƛ_20
                                                                       (coe v29))
                                                                    (coe v27))
                                                                 (coe v22))
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38 v15
                      -> case coe v15 of
                           MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inl_30 v19
                             -> case coe v19 of
                                  C_float'45'case_42 v26 v27
                                    -> case coe v1 of
                                         MAlonzo.Code.Untyped.C_case_40 v28 v29
                                           -> case coe v2 of
                                                MAlonzo.Code.Untyped.C__'183'__22 v30 v31
                                                  -> case coe v30 of
                                                       MAlonzo.Code.Untyped.C_ƛ_20 v32
                                                         -> case coe v32 of
                                                              MAlonzo.Code.Untyped.C_case_40 v33 v34
                                                                -> coe
                                                                     addInt
                                                                     (coe
                                                                        addInt (coe (1 :: Integer))
                                                                        (coe
                                                                           d_numSites'42'_338
                                                                           (coe
                                                                              addInt
                                                                              (coe (1 :: Integer))
                                                                              (coe v0))
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Base.du_map_22
                                                                              (coe
                                                                                 MAlonzo.Code.Untyped.RenamingSubstitution.d_weaken_88
                                                                                 (coe v0))
                                                                              (coe v29))
                                                                           (coe v34) (coe v27)))
                                                                     (coe
                                                                        d_numSites_330 (coe v0)
                                                                        (coe v28)
                                                                        (coe
                                                                           MAlonzo.Code.Untyped.C__'183'__22
                                                                           (coe
                                                                              MAlonzo.Code.Untyped.C_ƛ_20
                                                                              (coe v33))
                                                                           (coe v31))
                                                                        (coe v26))
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38 v19
                             -> case coe v19 of
                                  MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inl_30 v23
                                    -> case coe v23 of
                                         C_float'45'force_58 v28
                                           -> case coe v1 of
                                                MAlonzo.Code.Untyped.C_force_24 v29
                                                  -> case coe v2 of
                                                       MAlonzo.Code.Untyped.C__'183'__22 v30 v31
                                                         -> case coe v30 of
                                                              MAlonzo.Code.Untyped.C_ƛ_20 v32
                                                                -> case coe v32 of
                                                                     MAlonzo.Code.Untyped.C_force_24 v33
                                                                       -> coe
                                                                            addInt
                                                                            (coe (1 :: Integer))
                                                                            (coe
                                                                               d_numSites_330
                                                                               (coe v0) (coe v29)
                                                                               (coe
                                                                                  MAlonzo.Code.Untyped.C__'183'__22
                                                                                  (coe
                                                                                     MAlonzo.Code.Untyped.C_ƛ_20
                                                                                     (coe v33))
                                                                                  (coe v31))
                                                                               (coe v28))
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
-- VerifiedCompilation.FloatOut.numSites*
d_numSites'42'_338 ::
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Untyped.Relation.Binary.Core.T_Pointwise_20 -> Integer
d_numSites'42'_338 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Untyped.Relation.Binary.Core.C_'91''93'_26
        -> coe (0 :: Integer)
      MAlonzo.Code.Untyped.Relation.Binary.Core.C__'8759'__36 v8 v9
        -> case coe v1 of
             (:) v10 v11
               -> case coe v2 of
                    (:) v12 v13
                      -> coe
                           addInt
                           (coe d_numSites'42'_338 (coe v0) (coe v11) (coe v13) (coe v9))
                           (coe d_numSites_330 (coe v0) (coe v10) (coe v12) (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.FloatOut.numSites-compat
d_numSites'45'compat_346 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.Relation.Binary.Modular.T__'8853'__16 ->
  Integer
d_numSites'45'compat_346 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inl_30 v7
        -> coe seq (coe v7) (coe (0 :: Integer))
      MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38 v7
        -> case coe v7 of
             MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inl_30 v11
               -> case coe v11 of
                    MAlonzo.Code.Untyped.Relation.Binary.Modular.C_ƛF_132 v15
                      -> case coe v1 of
                           MAlonzo.Code.Untyped.C_ƛ_20 v16
                             -> case coe v2 of
                                  MAlonzo.Code.Untyped.C_ƛ_20 v17
                                    -> coe
                                         d_numSites_330 (coe addInt (coe (1 :: Integer)) (coe v0))
                                         (coe v16) (coe v17) (coe v15)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38 v11
               -> case coe v11 of
                    MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inl_30 v15
                      -> case coe v15 of
                           MAlonzo.Code.Untyped.Relation.Binary.Modular.C__'183'F__150 v21 v22
                             -> case coe v1 of
                                  MAlonzo.Code.Untyped.C__'183'__22 v23 v24
                                    -> case coe v2 of
                                         MAlonzo.Code.Untyped.C__'183'__22 v25 v26
                                           -> coe
                                                addInt
                                                (coe
                                                   d_numSites_330 (coe v0) (coe v23) (coe v25)
                                                   (coe v21))
                                                (coe
                                                   d_numSites_330 (coe v0) (coe v24) (coe v26)
                                                   (coe v22))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38 v15
                      -> case coe v15 of
                           MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inl_30 v19
                             -> case coe v19 of
                                  MAlonzo.Code.Untyped.Relation.Binary.Modular.C_forceF_164 v23
                                    -> case coe v1 of
                                         MAlonzo.Code.Untyped.C_force_24 v24
                                           -> case coe v2 of
                                                MAlonzo.Code.Untyped.C_force_24 v25
                                                  -> coe
                                                       d_numSites_330 (coe v0) (coe v24) (coe v25)
                                                       (coe v23)
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38 v19
                             -> case coe v19 of
                                  MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inl_30 v23
                                    -> case coe v23 of
                                         MAlonzo.Code.Untyped.Relation.Binary.Modular.C_delayF_178 v27
                                           -> case coe v1 of
                                                MAlonzo.Code.Untyped.C_delay_26 v28
                                                  -> case coe v2 of
                                                       MAlonzo.Code.Untyped.C_delay_26 v29
                                                         -> coe
                                                              d_numSites_330 (coe v0) (coe v28)
                                                              (coe v29) (coe v27)
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38 v23
                                    -> case coe v23 of
                                         MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inl_30 v27
                                           -> coe seq (coe v27) (coe (0 :: Integer))
                                         MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38 v27
                                           -> case coe v27 of
                                                MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inl_30 v31
                                                  -> case coe v31 of
                                                       MAlonzo.Code.Untyped.Relation.Binary.Modular.C_constrF_206 v36
                                                         -> case coe v1 of
                                                              MAlonzo.Code.Untyped.C_constr_34 v37 v38
                                                                -> case coe v2 of
                                                                     MAlonzo.Code.Untyped.C_constr_34 v39 v40
                                                                       -> coe
                                                                            d_numSites'42'_338
                                                                            (coe v0) (coe v38)
                                                                            (coe v40) (coe v36)
                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38 v31
                                                  -> case coe v31 of
                                                       MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inl_30 v35
                                                         -> case coe v35 of
                                                              MAlonzo.Code.Untyped.Relation.Binary.Modular.C_caseF_224 v41 v42
                                                                -> case coe v1 of
                                                                     MAlonzo.Code.Untyped.C_case_40 v43 v44
                                                                       -> case coe v2 of
                                                                            MAlonzo.Code.Untyped.C_case_40 v45 v46
                                                                              -> coe
                                                                                   addInt
                                                                                   (coe
                                                                                      d_numSites'42'_338
                                                                                      (coe v0)
                                                                                      (coe v44)
                                                                                      (coe v46)
                                                                                      (coe v42))
                                                                                   (coe
                                                                                      d_numSites_330
                                                                                      (coe v0)
                                                                                      (coe v43)
                                                                                      (coe v45)
                                                                                      (coe v41))
                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38 v35
                                                         -> case coe v35 of
                                                              MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inl_30 v39
                                                                -> coe
                                                                     seq (coe v39)
                                                                     (coe (0 :: Integer))
                                                              MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38 v39
                                                                -> case coe v39 of
                                                                     MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inl_30 v43
                                                                       -> coe
                                                                            seq (coe v43)
                                                                            (coe (0 :: Integer))
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
