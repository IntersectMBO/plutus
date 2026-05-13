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
      MAlonzo.Code.Untyped.Relation.Binary.Modular.du_Fix'45'dec_448
      (coe
         MAlonzo.Code.Untyped.Relation.Binary.Modular.du__'43''45'dec__360
         (\ v1 ->
            coe
              MAlonzo.Code.Untyped.Relation.Binary.Modular.du_compatTerm'63'_1120)
         (coe
            MAlonzo.Code.Untyped.Relation.Binary.Modular.du__'43''45'dec__360
            (\ v1 v2 v3 v4 v5 -> coe du_apply'45'dec_62 v2 v3 v4 v5)
            (coe
               MAlonzo.Code.Untyped.Relation.Binary.Modular.du__'43''45'dec__360
               (\ v1 v2 v3 v4 v5 -> coe du_case'45'dec_148 v2 v3 v4 v5)
               (\ v1 v2 v3 v4 v5 -> coe du_force'45'dec_234 v2 v3 v4 v5))))
      (coe v0)
-- VerifiedCompilation.FloatOut.decide
d_decide_312 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_38
d_decide_312 v0 v1 v2
  = let v3 = coe d_dec_304 v0 v1 v2 in
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
                          MAlonzo.Code.VerifiedCompilation.Trace.d_LetFloatOutT_44 v1 v2)
         _ -> MAlonzo.RTE.mazUnreachableError)
