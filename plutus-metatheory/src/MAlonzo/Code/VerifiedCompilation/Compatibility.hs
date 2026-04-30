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

module MAlonzo.Code.VerifiedCompilation.Compatibility where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Builtin
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Fin.Properties
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.RawU
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects
import qualified MAlonzo.Code.Untyped
import qualified MAlonzo.Code.Untyped.Equality
import qualified MAlonzo.Code.VerifiedCompilation.UntypedViews

-- VerifiedCompilation.Compatibility.Rel
d_Rel_4 :: Integer -> ()
d_Rel_4 = erased
-- VerifiedCompilation.Compatibility.CompatVar
d_CompatVar_28 a0 a1 a2 = ()
data T_CompatVar_28 = C_'96''7580'_34
-- VerifiedCompilation.Compatibility.CompatApply
d_CompatApply_40 a0 a1 a2 a3 = ()
data T_CompatApply_40 = C__'183''7580'__46 AgdaAny AgdaAny
-- VerifiedCompilation.Compatibility.CompatLam
d_CompatLam_52 a0 a1 a2 a3 = ()
newtype T_CompatLam_52 = C_ƛ'7580'_60 AgdaAny
-- VerifiedCompilation.Compatibility.CompatForce
d_CompatForce_66 a0 a1 a2 a3 = ()
newtype T_CompatForce_66 = C_force'7580'_70 AgdaAny
-- VerifiedCompilation.Compatibility.CompatDelay
d_CompatDelay_76 a0 a1 a2 a3 = ()
newtype T_CompatDelay_76 = C_delay'7580'_80 AgdaAny
-- VerifiedCompilation.Compatibility.CompatCase
d_CompatCase_86 a0 a1 a2 a3 = ()
data T_CompatCase_86
  = C_case'7580'_90 AgdaAny
                    MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
-- VerifiedCompilation.Compatibility.CompatConstr
d_CompatConstr_96 a0 a1 a2 a3 = ()
newtype T_CompatConstr_96
  = C_constr'7580'_102 MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
-- VerifiedCompilation.Compatibility.CompatCon
d_CompatCon_106 a0 a1 a2 = ()
data T_CompatCon_106 = C_con'7580'_112
-- VerifiedCompilation.Compatibility.CompatError
d_CompatError_116 a0 a1 a2 = ()
data T_CompatError_116 = C_error'7580'_120
-- VerifiedCompilation.Compatibility.CompatBuiltin
d_CompatBuiltin_124 a0 a1 a2 = ()
data T_CompatBuiltin_124 = C_builtin'7580'_130
-- VerifiedCompilation.Compatibility.CompatTerm
d_CompatTerm_134 ::
  Integer ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> ()
d_CompatTerm_134 = erased
-- VerifiedCompilation.Compatibility.compatVar?
d_compatVar'63'_142 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_compatVar'63'_142 ~v0 v1 v2 = du_compatVar'63'_142 v1 v2
du_compatVar'63'_142 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_compatVar'63'_142 v0 v1
  = let v2
          = \ v2 ->
              coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158 in
    coe
      (case coe v0 of
         MAlonzo.Code.Untyped.C_'96'_18 v3
           -> let v4 = coe v2 v3 in
              coe
                (case coe v4 of
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                     -> if coe v5
                          then case coe v6 of
                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v7
                                   -> coe
                                        seq (coe v7)
                                        (case coe v1 of
                                           MAlonzo.Code.Untyped.C_'96'_18 v8
                                             -> let v9
                                                      = coe
                                                          MAlonzo.Code.Data.Fin.Properties.du__'8799'__50
                                                          (coe v3) (coe v8) in
                                                coe
                                                  (case coe v9 of
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                                       -> if coe v10
                                                            then coe
                                                                   seq (coe v11)
                                                                   (coe
                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                      (coe v10)
                                                                      (coe
                                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                         (coe C_'96''7580'_34)))
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
                                                                                       -> coe
                                                                                            seq
                                                                                            (coe
                                                                                               v15)
                                                                                            (coe
                                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                               (coe
                                                                                                  v13)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                  (coe
                                                                                                     C_'96''7580'_34)))
                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                              else coe
                                                                                     seq (coe v14)
                                                                                     (coe
                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                        (coe v13)
                                                                                        (coe
                                                                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                           MAlonzo.Code.Untyped.C_ƛ_20 v8
                                             -> let v9
                                                      = coe
                                                          MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                coe
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                     (coe v9)
                                                     (coe
                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                           MAlonzo.Code.Untyped.C__'183'__22 v8 v9
                                             -> let v10
                                                      = coe
                                                          MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                coe
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                     (coe v10)
                                                     (coe
                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                           MAlonzo.Code.Untyped.C_force_24 v8
                                             -> let v9
                                                      = coe
                                                          MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                coe
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                     (coe v9)
                                                     (coe
                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                           MAlonzo.Code.Untyped.C_delay_26 v8
                                             -> let v9
                                                      = coe
                                                          MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                coe
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                     (coe v9)
                                                     (coe
                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                           MAlonzo.Code.Untyped.C_con_28 v8
                                             -> let v9
                                                      = coe
                                                          MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                coe
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                     (coe v9)
                                                     (coe
                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                           MAlonzo.Code.Untyped.C_constr_34 v8 v9
                                             -> let v10
                                                      = coe
                                                          MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                coe
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                     (coe v10)
                                                     (coe
                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                           MAlonzo.Code.Untyped.C_case_40 v8 v9
                                             -> let v10
                                                      = coe
                                                          MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                coe
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                     (coe v10)
                                                     (coe
                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                           MAlonzo.Code.Untyped.C_builtin_44 v8
                                             -> let v9
                                                      = coe
                                                          MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                coe
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                     (coe v9)
                                                     (coe
                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                           MAlonzo.Code.Untyped.C_error_46
                                             -> let v8
                                                      = coe
                                                          MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                coe
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                     (coe v8)
                                                     (coe
                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          else (let v7
                                      = seq
                                          (coe v6)
                                          (coe
                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                             (coe v5)
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                coe
                                  (case coe v7 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                       -> if coe v8
                                            then case coe v9 of
                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v10
                                                     -> case coe v10 of
                                                          MAlonzo.Code.VerifiedCompilation.UntypedViews.C_'96''33'_864 v12
                                                            -> coe
                                                                 seq (coe v12)
                                                                 (case coe v1 of
                                                                    MAlonzo.Code.Untyped.C_'96'_18 v13
                                                                      -> let v14
                                                                               = coe
                                                                                   MAlonzo.Code.Data.Fin.Properties.du__'8799'__50
                                                                                   (coe v3)
                                                                                   (coe v13) in
                                                                         coe
                                                                           (case coe v14 of
                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                                                                -> if coe v15
                                                                                     then coe
                                                                                            seq
                                                                                            (coe
                                                                                               v16)
                                                                                            (coe
                                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                               (coe
                                                                                                  v15)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                  (coe
                                                                                                     C_'96''7580'_34)))
                                                                                     else (let v17
                                                                                                 = seq
                                                                                                     (coe
                                                                                                        v16)
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                        (coe
                                                                                                           v15)
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                                                                           coe
                                                                                             (case coe
                                                                                                     v17 of
                                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                                                  -> if coe
                                                                                                          v18
                                                                                                       then case coe
                                                                                                                   v19 of
                                                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v20
                                                                                                                -> coe
                                                                                                                     seq
                                                                                                                     (coe
                                                                                                                        v20)
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                        (coe
                                                                                                                           v18)
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                                           (coe
                                                                                                                              C_'96''7580'_34)))
                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                       else coe
                                                                                                              seq
                                                                                                              (coe
                                                                                                                 v19)
                                                                                                              (coe
                                                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                 (coe
                                                                                                                    v18)
                                                                                                                 (coe
                                                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError))
                                                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                                                    MAlonzo.Code.Untyped.C_ƛ_20 v13
                                                                      -> coe
                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                           (coe v5)
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                    MAlonzo.Code.Untyped.C__'183'__22 v13 v14
                                                                      -> coe
                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                           (coe v5)
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                    MAlonzo.Code.Untyped.C_force_24 v13
                                                                      -> coe
                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                           (coe v5)
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                    MAlonzo.Code.Untyped.C_delay_26 v13
                                                                      -> coe
                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                           (coe v5)
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                    MAlonzo.Code.Untyped.C_con_28 v13
                                                                      -> coe
                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                           (coe v5)
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                    MAlonzo.Code.Untyped.C_constr_34 v13 v14
                                                                      -> coe
                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                           (coe v5)
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                    MAlonzo.Code.Untyped.C_case_40 v13 v14
                                                                      -> coe
                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                           (coe v5)
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                    MAlonzo.Code.Untyped.C_builtin_44 v13
                                                                      -> coe
                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                           (coe v5)
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                    MAlonzo.Code.Untyped.C_error_46
                                                                      -> coe
                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                           (coe v5)
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            else coe
                                                   seq (coe v9)
                                                   (coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                      (coe v8)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                     _ -> MAlonzo.RTE.mazUnreachableError))
                   _ -> MAlonzo.RTE.mazUnreachableError)
         MAlonzo.Code.Untyped.C_ƛ_20 v3
           -> let v4 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
              coe
                (coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                   (coe v4)
                   (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         MAlonzo.Code.Untyped.C__'183'__22 v3 v4
           -> let v5 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
              coe
                (coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                   (coe v5)
                   (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         MAlonzo.Code.Untyped.C_force_24 v3
           -> let v4 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
              coe
                (coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                   (coe v4)
                   (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         MAlonzo.Code.Untyped.C_delay_26 v3
           -> let v4 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
              coe
                (coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                   (coe v4)
                   (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         MAlonzo.Code.Untyped.C_con_28 v3
           -> let v4 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
              coe
                (coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                   (coe v4)
                   (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         MAlonzo.Code.Untyped.C_constr_34 v3 v4
           -> let v5 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
              coe
                (coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                   (coe v5)
                   (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         MAlonzo.Code.Untyped.C_case_40 v3 v4
           -> let v5 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
              coe
                (coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                   (coe v5)
                   (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         MAlonzo.Code.Untyped.C_builtin_44 v3
           -> let v4 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
              coe
                (coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                   (coe v4)
                   (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         MAlonzo.Code.Untyped.C_error_46
           -> let v3 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
              coe
                (coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                   (coe v3)
                   (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.Compatibility.compatApply?
d_compatApply'63'_188 ::
  Integer ->
  (MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_compatApply'63'_188 ~v0 ~v1 v2 v3 v4
  = du_compatApply'63'_188 v2 v3 v4
du_compatApply'63'_188 ::
  (MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_compatApply'63'_188 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
              (coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du__'183''63'__1230
                 (\ v3 ->
                    coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)
                 (\ v3 ->
                    coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)
                 (coe v1))
              (coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du__'183''63'__1230
                 (\ v3 ->
                    coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)
                 (\ v3 ->
                    coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)
                 (coe v2)) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then case coe v5 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v6
                         -> case coe v6 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                -> case coe v7 of
                                     MAlonzo.Code.VerifiedCompilation.UntypedViews.C__'183''33'__894 v11 v12
                                       -> case coe v1 of
                                            MAlonzo.Code.Untyped.C__'183'__22 v13 v14
                                              -> coe
                                                   seq (coe v11)
                                                   (coe
                                                      seq (coe v12)
                                                      (case coe v8 of
                                                         MAlonzo.Code.VerifiedCompilation.UntypedViews.C__'183''33'__894 v17 v18
                                                           -> case coe v2 of
                                                                MAlonzo.Code.Untyped.C__'183'__22 v19 v20
                                                                  -> coe
                                                                       seq (coe v17)
                                                                       (coe
                                                                          seq (coe v18)
                                                                          (let v21
                                                                                 = coe
                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                                                                                     (coe
                                                                                        v0 v13 v19)
                                                                                     (coe
                                                                                        v0 v14
                                                                                        v20) in
                                                                           coe
                                                                             (case coe v21 of
                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v22 v23
                                                                                  -> if coe v22
                                                                                       then case coe
                                                                                                   v23 of
                                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v24
                                                                                                -> case coe
                                                                                                          v24 of
                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                                                                                                       -> coe
                                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                            (coe
                                                                                                               v22)
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                               (coe
                                                                                                                  C__'183''7580'__46
                                                                                                                  v25
                                                                                                                  v26))
                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                       else coe
                                                                                              seq
                                                                                              (coe
                                                                                                 v23)
                                                                                              (coe
                                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                 (coe
                                                                                                    v22)
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                _ -> MAlonzo.RTE.mazUnreachableError)))
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         _ -> MAlonzo.RTE.mazUnreachableError))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v5)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                          (coe v4)
                          (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.Compatibility.compatLam?
d_compatLam'63'_278 ::
  Integer ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_compatLam'63'_278 v0 ~v1 v2 v3 v4
  = du_compatLam'63'_278 v0 v2 v3 v4
du_compatLam'63'_278 ::
  Integer ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_compatLam'63'_278 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
              (coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du_ƛ'63'_1128
                 (\ v4 ->
                    coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)
                 (coe v2))
              (coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du_ƛ'63'_1128
                 (\ v4 ->
                    coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)
                 (coe v3)) in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v7
                         -> case coe v7 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                -> case coe v8 of
                                     MAlonzo.Code.VerifiedCompilation.UntypedViews.C_ƛ'33'_876 v11
                                       -> case coe v2 of
                                            MAlonzo.Code.Untyped.C_ƛ_20 v12
                                              -> coe
                                                   seq (coe v11)
                                                   (case coe v9 of
                                                      MAlonzo.Code.VerifiedCompilation.UntypedViews.C_ƛ'33'_876 v14
                                                        -> case coe v3 of
                                                             MAlonzo.Code.Untyped.C_ƛ_20 v15
                                                               -> coe
                                                                    seq (coe v14)
                                                                    (let v16
                                                                           = coe
                                                                               v1
                                                                               (addInt
                                                                                  (coe
                                                                                     (1 :: Integer))
                                                                                  (coe v0))
                                                                               v12 v15 in
                                                                     coe
                                                                       (case coe v16 of
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                            -> if coe v17
                                                                                 then case coe
                                                                                             v18 of
                                                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v19
                                                                                          -> coe
                                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                               (coe
                                                                                                  v17)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                  (coe
                                                                                                     C_ƛ'7580'_60
                                                                                                     v19))
                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                 else coe
                                                                                        seq
                                                                                        (coe v18)
                                                                                        (coe
                                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                           (coe v17)
                                                                                           (coe
                                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                          _ -> MAlonzo.RTE.mazUnreachableError))
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
-- VerifiedCompilation.Compatibility.compatForce?
d_compatForce'63'_344 ::
  Integer ->
  (MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_compatForce'63'_344 ~v0 ~v1 v2 v3 v4
  = du_compatForce'63'_344 v2 v3 v4
du_compatForce'63'_344 ::
  (MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_compatForce'63'_344 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
              (coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du_force'63'_1344
                 (\ v3 ->
                    coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)
                 (coe v1))
              (coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du_force'63'_1344
                 (\ v3 ->
                    coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)
                 (coe v2)) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then case coe v5 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v6
                         -> case coe v6 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                -> case coe v7 of
                                     MAlonzo.Code.VerifiedCompilation.UntypedViews.C_force'33'_906 v10
                                       -> case coe v1 of
                                            MAlonzo.Code.Untyped.C_force_24 v11
                                              -> coe
                                                   seq (coe v10)
                                                   (case coe v8 of
                                                      MAlonzo.Code.VerifiedCompilation.UntypedViews.C_force'33'_906 v13
                                                        -> case coe v2 of
                                                             MAlonzo.Code.Untyped.C_force_24 v14
                                                               -> coe
                                                                    seq (coe v13)
                                                                    (let v15 = coe v0 v11 v14 in
                                                                     coe
                                                                       (case coe v15 of
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                            -> if coe v16
                                                                                 then case coe
                                                                                             v17 of
                                                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v18
                                                                                          -> coe
                                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                               (coe
                                                                                                  v16)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                  (coe
                                                                                                     C_force'7580'_70
                                                                                                     v18))
                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                 else coe
                                                                                        seq
                                                                                        (coe v17)
                                                                                        (coe
                                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                           (coe v16)
                                                                                           (coe
                                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                          _ -> MAlonzo.RTE.mazUnreachableError))
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v5)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                          (coe v4)
                          (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.Compatibility.compatDelay?
d_compatDelay'63'_410 ::
  Integer ->
  (MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_compatDelay'63'_410 ~v0 ~v1 v2 v3 v4
  = du_compatDelay'63'_410 v2 v3 v4
du_compatDelay'63'_410 ::
  (MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_compatDelay'63'_410 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
              (coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du_delay'63'_1422
                 (\ v3 ->
                    coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)
                 (coe v1))
              (coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du_delay'63'_1422
                 (\ v3 ->
                    coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)
                 (coe v2)) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then case coe v5 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v6
                         -> case coe v6 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                -> case coe v7 of
                                     MAlonzo.Code.VerifiedCompilation.UntypedViews.C_delay'33'_918 v10
                                       -> case coe v1 of
                                            MAlonzo.Code.Untyped.C_delay_26 v11
                                              -> coe
                                                   seq (coe v10)
                                                   (case coe v8 of
                                                      MAlonzo.Code.VerifiedCompilation.UntypedViews.C_delay'33'_918 v13
                                                        -> case coe v2 of
                                                             MAlonzo.Code.Untyped.C_delay_26 v14
                                                               -> coe
                                                                    seq (coe v13)
                                                                    (let v15 = coe v0 v11 v14 in
                                                                     coe
                                                                       (case coe v15 of
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                            -> if coe v16
                                                                                 then case coe
                                                                                             v17 of
                                                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v18
                                                                                          -> coe
                                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                               (coe
                                                                                                  v16)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                  (coe
                                                                                                     C_delay'7580'_80
                                                                                                     v18))
                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                 else coe
                                                                                        seq
                                                                                        (coe v17)
                                                                                        (coe
                                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                           (coe v16)
                                                                                           (coe
                                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                          _ -> MAlonzo.RTE.mazUnreachableError))
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v5)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                          (coe v4)
                          (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.Compatibility.pointwise?
d_pointwise'63'_488 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_pointwise'63'_488 ~v0 ~v1 ~v2 v3 v4 v5
  = du_pointwise'63'_488 v3 v4 v5
du_pointwise'63'_488 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_pointwise'63'_488 v0 v1 v2
  = case coe v1 of
      []
        -> case coe v2 of
             []
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe
                          MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C_'91''93'_56))
             (:) v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      (:) v3 v4
        -> case coe v2 of
             []
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             (:) v5 v6
               -> let v7
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                            (coe v0 v3 v5)
                            (coe du_pointwise'63'_488 (coe v0) (coe v4) (coe v6)) in
                  coe
                    (case coe v7 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                         -> if coe v8
                              then case coe v9 of
                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v10
                                       -> case coe v10 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                              -> coe
                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                   (coe v8)
                                                   (coe
                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62
                                                         v11 v12))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              else coe
                                     seq (coe v9)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v8)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.Compatibility.compatConstr?
d_compatConstr'63'_544 ::
  Integer ->
  (MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_compatConstr'63'_544 ~v0 ~v1 v2 v3 v4
  = du_compatConstr'63'_544 v2 v3 v4
du_compatConstr'63'_544 ::
  (MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_compatConstr'63'_544 v0 v1 v2
  = let v3
          = \ v3 ->
              coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158 in
    coe
      (let v4
             = \ v4 ->
                 coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158 in
       coe
         (case coe v1 of
            MAlonzo.Code.Untyped.C_'96'_18 v5
              -> let v6 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                 coe
                   (coe
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                      (coe v6)
                      (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
            MAlonzo.Code.Untyped.C_ƛ_20 v5
              -> let v6 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                 coe
                   (coe
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                      (coe v6)
                      (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
            MAlonzo.Code.Untyped.C__'183'__22 v5 v6
              -> let v7 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                 coe
                   (coe
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                      (coe v7)
                      (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
            MAlonzo.Code.Untyped.C_force_24 v5
              -> let v6 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                 coe
                   (coe
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                      (coe v6)
                      (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
            MAlonzo.Code.Untyped.C_delay_26 v5
              -> let v6 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                 coe
                   (coe
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                      (coe v6)
                      (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
            MAlonzo.Code.Untyped.C_con_28 v5
              -> let v6 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                 coe
                   (coe
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                      (coe v6)
                      (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
            MAlonzo.Code.Untyped.C_constr_34 v5 v6
              -> let v7
                       = coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                           (coe v3 v5) (coe v4 v6) in
                 coe
                   (case coe v7 of
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                        -> if coe v8
                             then case coe v9 of
                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v10
                                      -> case coe v10 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                             -> coe
                                                  seq (coe v11)
                                                  (coe
                                                     seq (coe v12)
                                                     (case coe v2 of
                                                        MAlonzo.Code.Untyped.C_'96'_18 v13
                                                          -> let v14
                                                                   = coe
                                                                       MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                             coe
                                                               (coe
                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                  (coe v14)
                                                                  (coe
                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                        MAlonzo.Code.Untyped.C_ƛ_20 v13
                                                          -> let v14
                                                                   = coe
                                                                       MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                             coe
                                                               (coe
                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                  (coe v14)
                                                                  (coe
                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                        MAlonzo.Code.Untyped.C__'183'__22 v13 v14
                                                          -> let v15
                                                                   = coe
                                                                       MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                             coe
                                                               (coe
                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                  (coe v15)
                                                                  (coe
                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                        MAlonzo.Code.Untyped.C_force_24 v13
                                                          -> let v14
                                                                   = coe
                                                                       MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                             coe
                                                               (coe
                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                  (coe v14)
                                                                  (coe
                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                        MAlonzo.Code.Untyped.C_delay_26 v13
                                                          -> let v14
                                                                   = coe
                                                                       MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                             coe
                                                               (coe
                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                  (coe v14)
                                                                  (coe
                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                        MAlonzo.Code.Untyped.C_con_28 v13
                                                          -> let v14
                                                                   = coe
                                                                       MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                             coe
                                                               (coe
                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                  (coe v14)
                                                                  (coe
                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                        MAlonzo.Code.Untyped.C_constr_34 v13 v14
                                                          -> let v15
                                                                   = coe
                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                                                                       (coe
                                                                          MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796
                                                                          (coe v5) (coe v13))
                                                                       (coe
                                                                          MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158) in
                                                             coe
                                                               (case coe v15 of
                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                    -> if coe v16
                                                                         then case coe v17 of
                                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v18
                                                                                  -> case coe v18 of
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                                         -> coe
                                                                                              seq
                                                                                              (coe
                                                                                                 v20)
                                                                                              (let v21
                                                                                                     = coe
                                                                                                         du_pointwise'63'_488
                                                                                                         (coe
                                                                                                            v0)
                                                                                                         (coe
                                                                                                            v6)
                                                                                                         (coe
                                                                                                            v14) in
                                                                                               coe
                                                                                                 (case coe
                                                                                                         v21 of
                                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v22 v23
                                                                                                      -> if coe
                                                                                                              v22
                                                                                                           then case coe
                                                                                                                       v23 of
                                                                                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v24
                                                                                                                    -> coe
                                                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                         (coe
                                                                                                                            v22)
                                                                                                                         (coe
                                                                                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                                            (coe
                                                                                                                               C_constr'7580'_102
                                                                                                                               v24))
                                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                           else coe
                                                                                                                  seq
                                                                                                                  (coe
                                                                                                                     v23)
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                     (coe
                                                                                                                        v22)
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                         else (let v18
                                                                                     = seq
                                                                                         (coe v17)
                                                                                         (coe
                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                            (coe
                                                                                               v16)
                                                                                            (coe
                                                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                                                               coe
                                                                                 (case coe v18 of
                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v19 v20
                                                                                      -> if coe v19
                                                                                           then case coe
                                                                                                       v20 of
                                                                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v21
                                                                                                    -> case coe
                                                                                                              v21 of
                                                                                                         MAlonzo.Code.VerifiedCompilation.UntypedViews.C_constr'33'_954 v24 v25
                                                                                                           -> coe
                                                                                                                seq
                                                                                                                (coe
                                                                                                                   v25)
                                                                                                                (let v26
                                                                                                                       = coe
                                                                                                                           du_pointwise'63'_488
                                                                                                                           (coe
                                                                                                                              v0)
                                                                                                                           (coe
                                                                                                                              v6)
                                                                                                                           (coe
                                                                                                                              v14) in
                                                                                                                 coe
                                                                                                                   (case coe
                                                                                                                           v26 of
                                                                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v27 v28
                                                                                                                        -> if coe
                                                                                                                                v27
                                                                                                                             then case coe
                                                                                                                                         v28 of
                                                                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v29
                                                                                                                                      -> coe
                                                                                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                                           (coe
                                                                                                                                              v27)
                                                                                                                                           (coe
                                                                                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                                                              (coe
                                                                                                                                                 C_constr'7580'_102
                                                                                                                                                 v29))
                                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                             else coe
                                                                                                                                    seq
                                                                                                                                    (coe
                                                                                                                                       v28)
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                                       (coe
                                                                                                                                          v27)
                                                                                                                                       (coe
                                                                                                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                           else coe
                                                                                                  seq
                                                                                                  (coe
                                                                                                     v20)
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                     (coe
                                                                                                        v19)
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError))
                                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                                        MAlonzo.Code.Untyped.C_case_40 v13 v14
                                                          -> let v15
                                                                   = coe
                                                                       MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                             coe
                                                               (coe
                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                  (coe v15)
                                                                  (coe
                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                        MAlonzo.Code.Untyped.C_builtin_44 v13
                                                          -> let v14
                                                                   = coe
                                                                       MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                             coe
                                                               (coe
                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                  (coe v14)
                                                                  (coe
                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                        MAlonzo.Code.Untyped.C_error_46
                                                          -> let v13
                                                                   = coe
                                                                       MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                             coe
                                                               (coe
                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                  (coe v13)
                                                                  (coe
                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                        _ -> MAlonzo.RTE.mazUnreachableError))
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             else (let v10
                                         = seq
                                             (coe v9)
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                (coe v8)
                                                (coe
                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                   coe
                                     (case coe v10 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                          -> if coe v11
                                               then case coe v12 of
                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v13
                                                        -> case coe v13 of
                                                             MAlonzo.Code.VerifiedCompilation.UntypedViews.C_constr'33'_954 v16 v17
                                                               -> coe
                                                                    seq (coe v16)
                                                                    (coe
                                                                       seq (coe v17)
                                                                       (case coe v2 of
                                                                          MAlonzo.Code.Untyped.C_'96'_18 v18
                                                                            -> coe
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                 (coe v8)
                                                                                 (coe
                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                          MAlonzo.Code.Untyped.C_ƛ_20 v18
                                                                            -> coe
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                 (coe v8)
                                                                                 (coe
                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                          MAlonzo.Code.Untyped.C__'183'__22 v18 v19
                                                                            -> coe
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                 (coe v8)
                                                                                 (coe
                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                          MAlonzo.Code.Untyped.C_force_24 v18
                                                                            -> coe
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                 (coe v8)
                                                                                 (coe
                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                          MAlonzo.Code.Untyped.C_delay_26 v18
                                                                            -> coe
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                 (coe v8)
                                                                                 (coe
                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                          MAlonzo.Code.Untyped.C_con_28 v18
                                                                            -> coe
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                 (coe v8)
                                                                                 (coe
                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                          MAlonzo.Code.Untyped.C_constr_34 v18 v19
                                                                            -> let v20
                                                                                     = coe
                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                                                                                         (coe
                                                                                            MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796
                                                                                            (coe v5)
                                                                                            (coe
                                                                                               v18))
                                                                                         (coe
                                                                                            MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158) in
                                                                               coe
                                                                                 (case coe v20 of
                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                                                                      -> if coe v21
                                                                                           then case coe
                                                                                                       v22 of
                                                                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v23
                                                                                                    -> case coe
                                                                                                              v23 of
                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                                                                                           -> coe
                                                                                                                seq
                                                                                                                (coe
                                                                                                                   v25)
                                                                                                                (let v26
                                                                                                                       = coe
                                                                                                                           du_pointwise'63'_488
                                                                                                                           (coe
                                                                                                                              v0)
                                                                                                                           (coe
                                                                                                                              v6)
                                                                                                                           (coe
                                                                                                                              v19) in
                                                                                                                 coe
                                                                                                                   (case coe
                                                                                                                           v26 of
                                                                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v27 v28
                                                                                                                        -> if coe
                                                                                                                                v27
                                                                                                                             then case coe
                                                                                                                                         v28 of
                                                                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v29
                                                                                                                                      -> coe
                                                                                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                                           (coe
                                                                                                                                              v27)
                                                                                                                                           (coe
                                                                                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                                                              (coe
                                                                                                                                                 C_constr'7580'_102
                                                                                                                                                 v29))
                                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                             else coe
                                                                                                                                    seq
                                                                                                                                    (coe
                                                                                                                                       v28)
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                                       (coe
                                                                                                                                          v27)
                                                                                                                                       (coe
                                                                                                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                           else (let v23
                                                                                                       = seq
                                                                                                           (coe
                                                                                                              v22)
                                                                                                           (coe
                                                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                              (coe
                                                                                                                 v21)
                                                                                                              (coe
                                                                                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                                                                                 coe
                                                                                                   (case coe
                                                                                                           v23 of
                                                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v24 v25
                                                                                                        -> if coe
                                                                                                                v24
                                                                                                             then case coe
                                                                                                                         v25 of
                                                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v26
                                                                                                                      -> case coe
                                                                                                                                v26 of
                                                                                                                           MAlonzo.Code.VerifiedCompilation.UntypedViews.C_constr'33'_954 v29 v30
                                                                                                                             -> coe
                                                                                                                                  seq
                                                                                                                                  (coe
                                                                                                                                     v30)
                                                                                                                                  (let v31
                                                                                                                                         = coe
                                                                                                                                             du_pointwise'63'_488
                                                                                                                                             (coe
                                                                                                                                                v0)
                                                                                                                                             (coe
                                                                                                                                                v6)
                                                                                                                                             (coe
                                                                                                                                                v19) in
                                                                                                                                   coe
                                                                                                                                     (case coe
                                                                                                                                             v31 of
                                                                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v32 v33
                                                                                                                                          -> if coe
                                                                                                                                                  v32
                                                                                                                                               then case coe
                                                                                                                                                           v33 of
                                                                                                                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v34
                                                                                                                                                        -> coe
                                                                                                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                                                             (coe
                                                                                                                                                                v32)
                                                                                                                                                             (coe
                                                                                                                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                                                                                (coe
                                                                                                                                                                   C_constr'7580'_102
                                                                                                                                                                   v34))
                                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                               else coe
                                                                                                                                                      seq
                                                                                                                                                      (coe
                                                                                                                                                         v33)
                                                                                                                                                      (coe
                                                                                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                                                         (coe
                                                                                                                                                            v32)
                                                                                                                                                         (coe
                                                                                                                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError
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
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                                          MAlonzo.Code.Untyped.C_case_40 v18 v19
                                                                            -> coe
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                 (coe v8)
                                                                                 (coe
                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                          MAlonzo.Code.Untyped.C_builtin_44 v18
                                                                            -> coe
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                 (coe v8)
                                                                                 (coe
                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                          MAlonzo.Code.Untyped.C_error_46
                                                                            -> coe
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                 (coe v8)
                                                                                 (coe
                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                          _ -> MAlonzo.RTE.mazUnreachableError))
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
                      _ -> MAlonzo.RTE.mazUnreachableError)
            MAlonzo.Code.Untyped.C_case_40 v5 v6
              -> let v7 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                 coe
                   (coe
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                      (coe v7)
                      (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
            MAlonzo.Code.Untyped.C_builtin_44 v5
              -> let v6 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                 coe
                   (coe
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                      (coe v6)
                      (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
            MAlonzo.Code.Untyped.C_error_46
              -> let v5 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                 coe
                   (coe
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                      (coe v5)
                      (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
            _ -> MAlonzo.RTE.mazUnreachableError))
-- VerifiedCompilation.Compatibility.compatCase?
d_compatCase'63'_644 ::
  Integer ->
  (MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_compatCase'63'_644 ~v0 ~v1 v2 v3 v4
  = du_compatCase'63'_644 v2 v3 v4
du_compatCase'63'_644 ::
  (MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_compatCase'63'_644 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
              (coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du_case'63'_1502
                 (\ v3 ->
                    coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)
                 (\ v3 ->
                    coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)
                 (coe v1))
              (coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du_case'63'_1502
                 (\ v3 ->
                    coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)
                 (\ v3 ->
                    coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)
                 (coe v2)) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then case coe v5 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v6
                         -> case coe v6 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                -> case coe v7 of
                                     MAlonzo.Code.VerifiedCompilation.UntypedViews.C_case'33'_936 v11 v12
                                       -> case coe v1 of
                                            MAlonzo.Code.Untyped.C_case_40 v13 v14
                                              -> coe
                                                   seq (coe v11)
                                                   (coe
                                                      seq (coe v12)
                                                      (case coe v8 of
                                                         MAlonzo.Code.VerifiedCompilation.UntypedViews.C_case'33'_936 v17 v18
                                                           -> case coe v2 of
                                                                MAlonzo.Code.Untyped.C_case_40 v19 v20
                                                                  -> coe
                                                                       seq (coe v17)
                                                                       (coe
                                                                          seq (coe v18)
                                                                          (let v21
                                                                                 = coe
                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                                                                                     (coe
                                                                                        v0 v13 v19)
                                                                                     (coe
                                                                                        du_pointwise'63'_488
                                                                                        (coe v0)
                                                                                        (coe v14)
                                                                                        (coe
                                                                                           v20)) in
                                                                           coe
                                                                             (case coe v21 of
                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v22 v23
                                                                                  -> if coe v22
                                                                                       then case coe
                                                                                                   v23 of
                                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v24
                                                                                                -> case coe
                                                                                                          v24 of
                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                                                                                                       -> coe
                                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                            (coe
                                                                                                               v22)
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                               (coe
                                                                                                                  C_case'7580'_90
                                                                                                                  v25
                                                                                                                  v26))
                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                       else coe
                                                                                              seq
                                                                                              (coe
                                                                                                 v23)
                                                                                              (coe
                                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                 (coe
                                                                                                    v22)
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                _ -> MAlonzo.RTE.mazUnreachableError)))
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         _ -> MAlonzo.RTE.mazUnreachableError))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v5)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                          (coe v4)
                          (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.Compatibility.compatCon?
d_compatCon'63'_724 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_compatCon'63'_724 ~v0 v1 v2 = du_compatCon'63'_724 v1 v2
du_compatCon'63'_724 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_compatCon'63'_724 v0 v1
  = let v2
          = \ v2 ->
              coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158 in
    coe
      (case coe v0 of
         MAlonzo.Code.Untyped.C_'96'_18 v3
           -> let v4 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
              coe
                (coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                   (coe v4)
                   (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         MAlonzo.Code.Untyped.C_ƛ_20 v3
           -> let v4 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
              coe
                (coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                   (coe v4)
                   (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         MAlonzo.Code.Untyped.C__'183'__22 v3 v4
           -> let v5 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
              coe
                (coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                   (coe v5)
                   (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         MAlonzo.Code.Untyped.C_force_24 v3
           -> let v4 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
              coe
                (coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                   (coe v4)
                   (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         MAlonzo.Code.Untyped.C_delay_26 v3
           -> let v4 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
              coe
                (coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                   (coe v4)
                   (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         MAlonzo.Code.Untyped.C_con_28 v3
           -> let v4 = coe v2 v3 in
              coe
                (case coe v4 of
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                     -> if coe v5
                          then case coe v6 of
                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v7
                                   -> coe
                                        seq (coe v7)
                                        (case coe v1 of
                                           MAlonzo.Code.Untyped.C_'96'_18 v8
                                             -> let v9
                                                      = coe
                                                          MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                coe
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                     (coe v9)
                                                     (coe
                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                           MAlonzo.Code.Untyped.C_ƛ_20 v8
                                             -> let v9
                                                      = coe
                                                          MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                coe
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                     (coe v9)
                                                     (coe
                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                           MAlonzo.Code.Untyped.C__'183'__22 v8 v9
                                             -> let v10
                                                      = coe
                                                          MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                coe
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                     (coe v10)
                                                     (coe
                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                           MAlonzo.Code.Untyped.C_force_24 v8
                                             -> let v9
                                                      = coe
                                                          MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                coe
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                     (coe v9)
                                                     (coe
                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                           MAlonzo.Code.Untyped.C_delay_26 v8
                                             -> let v9
                                                      = coe
                                                          MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                coe
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                     (coe v9)
                                                     (coe
                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                           MAlonzo.Code.Untyped.C_con_28 v8
                                             -> let v9
                                                      = MAlonzo.Code.Untyped.Equality.d_decEq'45'TmCon_48
                                                          (coe v3) (coe v8) in
                                                coe
                                                  (case coe v9 of
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                                       -> if coe v10
                                                            then coe
                                                                   seq (coe v11)
                                                                   (coe
                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                      (coe v10)
                                                                      (coe
                                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                         (coe C_con'7580'_112)))
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
                                                                                       -> coe
                                                                                            seq
                                                                                            (coe
                                                                                               v15)
                                                                                            (coe
                                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                               (coe
                                                                                                  v13)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                  (coe
                                                                                                     C_con'7580'_112)))
                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                              else coe
                                                                                     seq (coe v14)
                                                                                     (coe
                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                        (coe v13)
                                                                                        (coe
                                                                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                           MAlonzo.Code.Untyped.C_constr_34 v8 v9
                                             -> let v10
                                                      = coe
                                                          MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                coe
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                     (coe v10)
                                                     (coe
                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                           MAlonzo.Code.Untyped.C_case_40 v8 v9
                                             -> let v10
                                                      = coe
                                                          MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                coe
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                     (coe v10)
                                                     (coe
                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                           MAlonzo.Code.Untyped.C_builtin_44 v8
                                             -> let v9
                                                      = coe
                                                          MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                coe
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                     (coe v9)
                                                     (coe
                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                           MAlonzo.Code.Untyped.C_error_46
                                             -> let v8
                                                      = coe
                                                          MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                coe
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                     (coe v8)
                                                     (coe
                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          else (let v7
                                      = seq
                                          (coe v6)
                                          (coe
                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                             (coe v5)
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                coe
                                  (case coe v7 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                       -> if coe v8
                                            then case coe v9 of
                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v10
                                                     -> case coe v10 of
                                                          MAlonzo.Code.VerifiedCompilation.UntypedViews.C_con'33'_964 v13
                                                            -> coe
                                                                 seq (coe v13)
                                                                 (case coe v1 of
                                                                    MAlonzo.Code.Untyped.C_'96'_18 v14
                                                                      -> coe
                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                           (coe v5)
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                    MAlonzo.Code.Untyped.C_ƛ_20 v14
                                                                      -> coe
                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                           (coe v5)
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                    MAlonzo.Code.Untyped.C__'183'__22 v14 v15
                                                                      -> coe
                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                           (coe v5)
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                    MAlonzo.Code.Untyped.C_force_24 v14
                                                                      -> coe
                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                           (coe v5)
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                    MAlonzo.Code.Untyped.C_delay_26 v14
                                                                      -> coe
                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                           (coe v5)
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                    MAlonzo.Code.Untyped.C_con_28 v14
                                                                      -> let v15
                                                                               = MAlonzo.Code.Untyped.Equality.d_decEq'45'TmCon_48
                                                                                   (coe v3)
                                                                                   (coe v14) in
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
                                                                                                     C_con'7580'_112)))
                                                                                     else (let v18
                                                                                                 = seq
                                                                                                     (coe
                                                                                                        v17)
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                        (coe
                                                                                                           v16)
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                                                                           coe
                                                                                             (case coe
                                                                                                     v18 of
                                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v19 v20
                                                                                                  -> if coe
                                                                                                          v19
                                                                                                       then case coe
                                                                                                                   v20 of
                                                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v21
                                                                                                                -> coe
                                                                                                                     seq
                                                                                                                     (coe
                                                                                                                        v21)
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                        (coe
                                                                                                                           v19)
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                                           (coe
                                                                                                                              C_con'7580'_112)))
                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                       else coe
                                                                                                              seq
                                                                                                              (coe
                                                                                                                 v20)
                                                                                                              (coe
                                                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                 (coe
                                                                                                                    v19)
                                                                                                                 (coe
                                                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError))
                                                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                                                    MAlonzo.Code.Untyped.C_constr_34 v14 v15
                                                                      -> coe
                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                           (coe v5)
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                    MAlonzo.Code.Untyped.C_case_40 v14 v15
                                                                      -> coe
                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                           (coe v5)
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                    MAlonzo.Code.Untyped.C_builtin_44 v14
                                                                      -> coe
                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                           (coe v5)
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                    MAlonzo.Code.Untyped.C_error_46
                                                                      -> coe
                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                           (coe v5)
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            else coe
                                                   seq (coe v9)
                                                   (coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                      (coe v8)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                     _ -> MAlonzo.RTE.mazUnreachableError))
                   _ -> MAlonzo.RTE.mazUnreachableError)
         MAlonzo.Code.Untyped.C_constr_34 v3 v4
           -> let v5 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
              coe
                (coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                   (coe v5)
                   (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         MAlonzo.Code.Untyped.C_case_40 v3 v4
           -> let v5 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
              coe
                (coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                   (coe v5)
                   (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         MAlonzo.Code.Untyped.C_builtin_44 v3
           -> let v4 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
              coe
                (coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                   (coe v4)
                   (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         MAlonzo.Code.Untyped.C_error_46
           -> let v3 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
              coe
                (coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                   (coe v3)
                   (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.Compatibility.compatBuiltin?
d_compatBuiltin'63'_768 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_compatBuiltin'63'_768 ~v0 v1 v2 = du_compatBuiltin'63'_768 v1 v2
du_compatBuiltin'63'_768 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_compatBuiltin'63'_768 v0 v1
  = let v2
          = \ v2 ->
              coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158 in
    coe
      (case coe v0 of
         MAlonzo.Code.Untyped.C_'96'_18 v3
           -> let v4 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
              coe
                (coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                   (coe v4)
                   (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         MAlonzo.Code.Untyped.C_ƛ_20 v3
           -> let v4 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
              coe
                (coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                   (coe v4)
                   (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         MAlonzo.Code.Untyped.C__'183'__22 v3 v4
           -> let v5 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
              coe
                (coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                   (coe v5)
                   (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         MAlonzo.Code.Untyped.C_force_24 v3
           -> let v4 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
              coe
                (coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                   (coe v4)
                   (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         MAlonzo.Code.Untyped.C_delay_26 v3
           -> let v4 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
              coe
                (coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                   (coe v4)
                   (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         MAlonzo.Code.Untyped.C_con_28 v3
           -> let v4 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
              coe
                (coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                   (coe v4)
                   (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         MAlonzo.Code.Untyped.C_constr_34 v3 v4
           -> let v5 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
              coe
                (coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                   (coe v5)
                   (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         MAlonzo.Code.Untyped.C_case_40 v3 v4
           -> let v5 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
              coe
                (coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                   (coe v5)
                   (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         MAlonzo.Code.Untyped.C_builtin_44 v3
           -> let v4 = coe v2 v3 in
              coe
                (case coe v4 of
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                     -> if coe v5
                          then case coe v6 of
                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v7
                                   -> coe
                                        seq (coe v7)
                                        (case coe v1 of
                                           MAlonzo.Code.Untyped.C_'96'_18 v8
                                             -> let v9
                                                      = coe
                                                          MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                coe
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                     (coe v9)
                                                     (coe
                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                           MAlonzo.Code.Untyped.C_ƛ_20 v8
                                             -> let v9
                                                      = coe
                                                          MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                coe
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                     (coe v9)
                                                     (coe
                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                           MAlonzo.Code.Untyped.C__'183'__22 v8 v9
                                             -> let v10
                                                      = coe
                                                          MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                coe
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                     (coe v10)
                                                     (coe
                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                           MAlonzo.Code.Untyped.C_force_24 v8
                                             -> let v9
                                                      = coe
                                                          MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                coe
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                     (coe v9)
                                                     (coe
                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                           MAlonzo.Code.Untyped.C_delay_26 v8
                                             -> let v9
                                                      = coe
                                                          MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                coe
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                     (coe v9)
                                                     (coe
                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                           MAlonzo.Code.Untyped.C_con_28 v8
                                             -> let v9
                                                      = coe
                                                          MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                coe
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                     (coe v9)
                                                     (coe
                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                           MAlonzo.Code.Untyped.C_constr_34 v8 v9
                                             -> let v10
                                                      = coe
                                                          MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                coe
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                     (coe v10)
                                                     (coe
                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                           MAlonzo.Code.Untyped.C_case_40 v8 v9
                                             -> let v10
                                                      = coe
                                                          MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                coe
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                     (coe v10)
                                                     (coe
                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                           MAlonzo.Code.Untyped.C_builtin_44 v8
                                             -> let v9
                                                      = MAlonzo.Code.Builtin.d_decBuiltin_440
                                                          (coe v3) (coe v8) in
                                                coe
                                                  (case coe v9 of
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                                       -> if coe v10
                                                            then coe
                                                                   seq (coe v11)
                                                                   (coe
                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                      (coe v10)
                                                                      (coe
                                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                         (coe C_builtin'7580'_130)))
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
                                                                                       -> coe
                                                                                            seq
                                                                                            (coe
                                                                                               v15)
                                                                                            (coe
                                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                               (coe
                                                                                                  v13)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                  (coe
                                                                                                     C_builtin'7580'_130)))
                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                              else coe
                                                                                     seq (coe v14)
                                                                                     (coe
                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                        (coe v13)
                                                                                        (coe
                                                                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                           MAlonzo.Code.Untyped.C_error_46
                                             -> let v8
                                                      = coe
                                                          MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                coe
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                     (coe v8)
                                                     (coe
                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          else (let v7
                                      = seq
                                          (coe v6)
                                          (coe
                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                             (coe v5)
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                coe
                                  (case coe v7 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                       -> if coe v8
                                            then case coe v9 of
                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v10
                                                     -> case coe v10 of
                                                          MAlonzo.Code.VerifiedCompilation.UntypedViews.C_builtin'33'_974 v13
                                                            -> coe
                                                                 seq (coe v13)
                                                                 (case coe v1 of
                                                                    MAlonzo.Code.Untyped.C_'96'_18 v14
                                                                      -> coe
                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                           (coe v5)
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                    MAlonzo.Code.Untyped.C_ƛ_20 v14
                                                                      -> coe
                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                           (coe v5)
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                    MAlonzo.Code.Untyped.C__'183'__22 v14 v15
                                                                      -> coe
                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                           (coe v5)
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                    MAlonzo.Code.Untyped.C_force_24 v14
                                                                      -> coe
                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                           (coe v5)
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                    MAlonzo.Code.Untyped.C_delay_26 v14
                                                                      -> coe
                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                           (coe v5)
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                    MAlonzo.Code.Untyped.C_con_28 v14
                                                                      -> coe
                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                           (coe v5)
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                    MAlonzo.Code.Untyped.C_constr_34 v14 v15
                                                                      -> coe
                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                           (coe v5)
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                    MAlonzo.Code.Untyped.C_case_40 v14 v15
                                                                      -> coe
                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                           (coe v5)
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                    MAlonzo.Code.Untyped.C_builtin_44 v14
                                                                      -> let v15
                                                                               = MAlonzo.Code.Builtin.d_decBuiltin_440
                                                                                   (coe v3)
                                                                                   (coe v14) in
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
                                                                                                     C_builtin'7580'_130)))
                                                                                     else (let v18
                                                                                                 = seq
                                                                                                     (coe
                                                                                                        v17)
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                        (coe
                                                                                                           v16)
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                                                                           coe
                                                                                             (case coe
                                                                                                     v18 of
                                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v19 v20
                                                                                                  -> if coe
                                                                                                          v19
                                                                                                       then case coe
                                                                                                                   v20 of
                                                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v21
                                                                                                                -> coe
                                                                                                                     seq
                                                                                                                     (coe
                                                                                                                        v21)
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                        (coe
                                                                                                                           v19)
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                                           (coe
                                                                                                                              C_builtin'7580'_130)))
                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                       else coe
                                                                                                              seq
                                                                                                              (coe
                                                                                                                 v20)
                                                                                                              (coe
                                                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                 (coe
                                                                                                                    v19)
                                                                                                                 (coe
                                                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError))
                                                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                                                    MAlonzo.Code.Untyped.C_error_46
                                                                      -> coe
                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                           (coe v5)
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            else coe
                                                   seq (coe v9)
                                                   (coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                      (coe v8)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                     _ -> MAlonzo.RTE.mazUnreachableError))
                   _ -> MAlonzo.RTE.mazUnreachableError)
         MAlonzo.Code.Untyped.C_error_46
           -> let v3 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
              coe
                (coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                   (coe v3)
                   (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.Compatibility.compatError?
d_compatError'63'_812 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_compatError'63'_812 ~v0 v1 v2 = du_compatError'63'_812 v1 v2
du_compatError'63'_812 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_compatError'63'_812 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
              (coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du_error'63'_1886
                 (coe v0))
              (coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du_error'63'_1886
                 (coe v1)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then case coe v4 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v5
                         -> case coe v5 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                                -> coe
                                     seq (coe v6)
                                     (coe
                                        seq (coe v7)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                           (coe v3)
                                           (coe
                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                              erased)))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v4)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                          (coe v3)
                          (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.Compatibility.compatTerm?
d_compatTerm'63'_842 ::
  Integer ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_compatTerm'63'_842 v0 ~v1 v2 v3 v4
  = du_compatTerm'63'_842 v0 v2 v3 v4
du_compatTerm'63'_842 ::
  Integer ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_compatTerm'63'_842 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'8846''45'dec__96
      (coe du_compatApply'63'_188 (coe v1 v0) (coe v2) (coe v3))
      (coe
         MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'8846''45'dec__96
         (coe du_compatVar'63'_142 (coe v2) (coe v3))
         (coe
            MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'8846''45'dec__96
            (coe du_compatLam'63'_278 (coe v0) (coe v1) (coe v2) (coe v3))
            (coe
               MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'8846''45'dec__96
               (coe du_compatForce'63'_344 (coe v1 v0) (coe v2) (coe v3))
               (coe
                  MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'8846''45'dec__96
                  (coe du_compatDelay'63'_410 (coe v1 v0) (coe v2) (coe v3))
                  (coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'8846''45'dec__96
                     (coe du_compatConstr'63'_544 (coe v1 v0) (coe v2) (coe v3))
                     (coe
                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'8846''45'dec__96
                        (coe du_compatCase'63'_644 (coe v1 v0) (coe v2) (coe v3))
                        (coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'8846''45'dec__96
                           (coe du_compatCon'63'_724 (coe v2) (coe v3))
                           (coe
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'8846''45'dec__96
                              (coe du_compatBuiltin'63'_768 (coe v2) (coe v3))
                              (coe du_compatError'63'_812 (coe v2) (coe v3))))))))))
