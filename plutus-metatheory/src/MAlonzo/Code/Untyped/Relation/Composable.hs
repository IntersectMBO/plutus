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

module MAlonzo.Code.Untyped.Relation.Composable where

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
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.RawU
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects
import qualified MAlonzo.Code.Untyped
import qualified MAlonzo.Code.Untyped.Equality
import qualified MAlonzo.Code.Untyped.Relation
import qualified MAlonzo.Code.Untyped.Relation.Pointwise
import qualified MAlonzo.Code.VerifiedCompilation.UntypedViews

-- Untyped.Relation.Composable.CompatVar
d_CompatVar_8 a0 a1 a2 a3 = ()
data T_CompatVar_8 = C_'96'F__16
-- Untyped.Relation.Composable.CompatLambda
d_CompatLambda_20 a0 a1 a2 a3 = ()
newtype T_CompatLambda_20 = C_ƛF_30 AgdaAny
-- Untyped.Relation.Composable.CompatApply
d_CompatApply_34 a0 a1 a2 a3 = ()
data T_CompatApply_34 = C__'183'F__48 AgdaAny AgdaAny
-- Untyped.Relation.Composable.CompatForce
d_CompatForce_52 a0 a1 a2 a3 = ()
newtype T_CompatForce_52 = C_forceF_62 AgdaAny
-- Untyped.Relation.Composable.CompatDelay
d_CompatDelay_66 a0 a1 a2 a3 = ()
newtype T_CompatDelay_66 = C_delayF_76 AgdaAny
-- Untyped.Relation.Composable.CompatCon
d_CompatCon_80 a0 a1 a2 a3 = ()
data T_CompatCon_80 = C_conF_88
-- Untyped.Relation.Composable.CompatConstr
d_CompatConstr_92 a0 a1 a2 a3 = ()
newtype T_CompatConstr_92
  = C_constrF_104 MAlonzo.Code.Untyped.Relation.Pointwise.T_Pointwise_10
-- Untyped.Relation.Composable.CompatCase
d_CompatCase_108 a0 a1 a2 a3 = ()
data T_CompatCase_108
  = C_caseF_122 AgdaAny
                MAlonzo.Code.Untyped.Relation.Pointwise.T_Pointwise_10
-- Untyped.Relation.Composable.CompatBuiltin
d_CompatBuiltin_126 a0 a1 a2 a3 = ()
data T_CompatBuiltin_126 = C_builtinF_134
-- Untyped.Relation.Composable.CompatError
d_CompatError_138 a0 a1 a2 a3 = ()
data T_CompatError_138 = C_errorF_144
-- Untyped.Relation.Composable.CompatTerm
d_CompatTerm_146 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> ()
d_CompatTerm_146 = erased
-- Untyped.Relation.Composable.Transitivity
d_Transitivity_150 a0 a1 a2 a3 = ()
data T_Transitivity_150
  = C_transF_162 MAlonzo.Code.Untyped.T__'8866'_14 AgdaAny AgdaAny
-- Untyped.Relation.Composable.Symmetry
d_Symmetry_166 a0 a1 a2 a3 = ()
newtype T_Symmetry_166 = C_symF_176 AgdaAny
-- Untyped.Relation.Composable.Reflexivity
d_Reflexivity_180 a0 a1 a2 a3 = ()
data T_Reflexivity_180 = C_reflF_188
-- Untyped.Relation.Composable.CompatTerm-TermCompatible
d_CompatTerm'45'TermCompatible_276 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.Relation.T__'43'__10 -> AgdaAny) ->
  MAlonzo.Code.Untyped.Relation.T_TermCompatible_194
d_CompatTerm'45'TermCompatible_276 ~v0 v1
  = du_CompatTerm'45'TermCompatible_276 v1
du_CompatTerm'45'TermCompatible_276 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.Relation.T__'43'__10 -> AgdaAny) ->
  MAlonzo.Code.Untyped.Relation.T_TermCompatible_194
du_CompatTerm'45'TermCompatible_276 v0
  = coe
      MAlonzo.Code.Untyped.Relation.C_constructor_314
      (coe
         (\ v1 v2 ->
            coe
              v0 v1 (coe MAlonzo.Code.Untyped.C_'96'_18 (coe v2))
              (coe MAlonzo.Code.Untyped.C_'96'_18 (coe v2))
              (coe MAlonzo.Code.Untyped.Relation.C_inl_24 (coe C_'96'F__16))))
      (coe
         (\ v1 v2 v3 v4 ->
            coe
              v0 v1 (coe MAlonzo.Code.Untyped.C_ƛ_20 (coe v2))
              (coe MAlonzo.Code.Untyped.C_ƛ_20 (coe v3))
              (coe
                 MAlonzo.Code.Untyped.Relation.C_inr_32
                 (coe MAlonzo.Code.Untyped.Relation.C_inl_24 (coe C_ƛF_30 v4)))))
      (coe
         (\ v1 v2 v3 v4 v5 v6 v7 ->
            coe
              v0 v1 (coe MAlonzo.Code.Untyped.C__'183'__22 (coe v2) (coe v4))
              (coe MAlonzo.Code.Untyped.C__'183'__22 (coe v3) (coe v5))
              (coe
                 MAlonzo.Code.Untyped.Relation.C_inr_32
                 (coe
                    MAlonzo.Code.Untyped.Relation.C_inr_32
                    (coe
                       MAlonzo.Code.Untyped.Relation.C_inl_24
                       (coe C__'183'F__48 v6 v7))))))
      (coe
         (\ v1 v2 v3 v4 ->
            coe
              v0 v1 (coe MAlonzo.Code.Untyped.C_force_24 (coe v2))
              (coe MAlonzo.Code.Untyped.C_force_24 (coe v3))
              (coe
                 MAlonzo.Code.Untyped.Relation.C_inr_32
                 (coe
                    MAlonzo.Code.Untyped.Relation.C_inr_32
                    (coe
                       MAlonzo.Code.Untyped.Relation.C_inr_32
                       (coe
                          MAlonzo.Code.Untyped.Relation.C_inl_24 (coe C_forceF_62 v4)))))))
      (coe
         (\ v1 v2 v3 v4 ->
            coe
              v0 v1 (coe MAlonzo.Code.Untyped.C_delay_26 (coe v2))
              (coe MAlonzo.Code.Untyped.C_delay_26 (coe v3))
              (coe
                 MAlonzo.Code.Untyped.Relation.C_inr_32
                 (coe
                    MAlonzo.Code.Untyped.Relation.C_inr_32
                    (coe
                       MAlonzo.Code.Untyped.Relation.C_inr_32
                       (coe
                          MAlonzo.Code.Untyped.Relation.C_inr_32
                          (coe
                             MAlonzo.Code.Untyped.Relation.C_inl_24 (coe C_delayF_76 v4))))))))
      (coe
         (\ v1 v2 v3 v4 v5 ->
            coe
              v0 v1 (coe MAlonzo.Code.Untyped.C_constr_34 (coe v2) (coe v3))
              (coe MAlonzo.Code.Untyped.C_constr_34 (coe v2) (coe v4))
              (coe
                 MAlonzo.Code.Untyped.Relation.C_inr_32
                 (coe
                    MAlonzo.Code.Untyped.Relation.C_inr_32
                    (coe
                       MAlonzo.Code.Untyped.Relation.C_inr_32
                       (coe
                          MAlonzo.Code.Untyped.Relation.C_inr_32
                          (coe
                             MAlonzo.Code.Untyped.Relation.C_inr_32
                             (coe
                                MAlonzo.Code.Untyped.Relation.C_inr_32
                                (coe
                                   MAlonzo.Code.Untyped.Relation.C_inl_24
                                   (coe C_constrF_104 v5))))))))))
      (coe
         (\ v1 v2 v3 v4 v5 v6 v7 ->
            coe
              v0 v1 (coe MAlonzo.Code.Untyped.C_case_40 (coe v2) (coe v4))
              (coe MAlonzo.Code.Untyped.C_case_40 (coe v3) (coe v5))
              (coe
                 MAlonzo.Code.Untyped.Relation.C_inr_32
                 (coe
                    MAlonzo.Code.Untyped.Relation.C_inr_32
                    (coe
                       MAlonzo.Code.Untyped.Relation.C_inr_32
                       (coe
                          MAlonzo.Code.Untyped.Relation.C_inr_32
                          (coe
                             MAlonzo.Code.Untyped.Relation.C_inr_32
                             (coe
                                MAlonzo.Code.Untyped.Relation.C_inr_32
                                (coe
                                   MAlonzo.Code.Untyped.Relation.C_inr_32
                                   (coe
                                      MAlonzo.Code.Untyped.Relation.C_inl_24
                                      (coe C_caseF_122 v6 v7)))))))))))
      (coe
         (\ v1 v2 ->
            coe
              v0 v2 (coe MAlonzo.Code.Untyped.C_con_28 (coe v1))
              (coe MAlonzo.Code.Untyped.C_con_28 (coe v1))
              (coe
                 MAlonzo.Code.Untyped.Relation.C_inr_32
                 (coe
                    MAlonzo.Code.Untyped.Relation.C_inr_32
                    (coe
                       MAlonzo.Code.Untyped.Relation.C_inr_32
                       (coe
                          MAlonzo.Code.Untyped.Relation.C_inr_32
                          (coe
                             MAlonzo.Code.Untyped.Relation.C_inr_32
                             (coe MAlonzo.Code.Untyped.Relation.C_inl_24 (coe C_conF_88)))))))))
      (coe
         (\ v1 v2 ->
            coe
              v0 v1 (coe MAlonzo.Code.Untyped.C_builtin_44 (coe v2))
              (coe MAlonzo.Code.Untyped.C_builtin_44 (coe v2))
              (coe
                 MAlonzo.Code.Untyped.Relation.C_inr_32
                 (coe
                    MAlonzo.Code.Untyped.Relation.C_inr_32
                    (coe
                       MAlonzo.Code.Untyped.Relation.C_inr_32
                       (coe
                          MAlonzo.Code.Untyped.Relation.C_inr_32
                          (coe
                             MAlonzo.Code.Untyped.Relation.C_inr_32
                             (coe
                                MAlonzo.Code.Untyped.Relation.C_inr_32
                                (coe
                                   MAlonzo.Code.Untyped.Relation.C_inr_32
                                   (coe
                                      MAlonzo.Code.Untyped.Relation.C_inr_32
                                      (coe
                                         MAlonzo.Code.Untyped.Relation.C_inl_24
                                         (coe C_builtinF_134))))))))))))
      (coe
         (\ v1 ->
            coe
              v0 v1 (coe MAlonzo.Code.Untyped.C_error_46)
              (coe MAlonzo.Code.Untyped.C_error_46)
              (coe
                 MAlonzo.Code.Untyped.Relation.C_inr_32
                 (coe
                    MAlonzo.Code.Untyped.Relation.C_inr_32
                    (coe
                       MAlonzo.Code.Untyped.Relation.C_inr_32
                       (coe
                          MAlonzo.Code.Untyped.Relation.C_inr_32
                          (coe
                             MAlonzo.Code.Untyped.Relation.C_inr_32
                             (coe
                                MAlonzo.Code.Untyped.Relation.C_inr_32
                                (coe
                                   MAlonzo.Code.Untyped.Relation.C_inr_32
                                   (coe
                                      MAlonzo.Code.Untyped.Relation.C_inr_32
                                      (coe
                                         MAlonzo.Code.Untyped.Relation.C_inr_32
                                         (coe
                                            MAlonzo.Code.Untyped.Relation.C_inl_24
                                            (coe C_errorF_144)))))))))))))
-- Untyped.Relation.Composable.DecidableRel
d_DecidableRel_296 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  ()
d_DecidableRel_296 = erased
-- Untyped.Relation.Composable.DecidableT
d_DecidableT_306 ::
  ((Integer ->
    MAlonzo.Code.Untyped.T__'8866'_14 ->
    MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
   Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  ()
d_DecidableT_306 = erased
-- Untyped.Relation.Composable._+-dec_
d__'43''45'dec__318 ::
  ((Integer ->
    MAlonzo.Code.Untyped.T__'8866'_14 ->
    MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
   Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  ((Integer ->
    MAlonzo.Code.Untyped.T__'8866'_14 ->
    MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
   Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  ((Integer ->
    MAlonzo.Code.Untyped.T__'8866'_14 ->
    MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
   (Integer ->
    MAlonzo.Code.Untyped.T__'8866'_14 ->
    MAlonzo.Code.Untyped.T__'8866'_14 ->
    MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
   Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  ((Integer ->
    MAlonzo.Code.Untyped.T__'8866'_14 ->
    MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
   (Integer ->
    MAlonzo.Code.Untyped.T__'8866'_14 ->
    MAlonzo.Code.Untyped.T__'8866'_14 ->
    MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
   Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
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
d__'43''45'dec__318 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8
  = du__'43''45'dec__318 v2 v3 v4 v5 v6 v7 v8
du__'43''45'dec__318 ::
  ((Integer ->
    MAlonzo.Code.Untyped.T__'8866'_14 ->
    MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
   (Integer ->
    MAlonzo.Code.Untyped.T__'8866'_14 ->
    MAlonzo.Code.Untyped.T__'8866'_14 ->
    MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
   Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  ((Integer ->
    MAlonzo.Code.Untyped.T__'8866'_14 ->
    MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
   (Integer ->
    MAlonzo.Code.Untyped.T__'8866'_14 ->
    MAlonzo.Code.Untyped.T__'8866'_14 ->
    MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
   Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
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
du__'43''45'dec__318 v0 v1 v2 v3 v4 v5 v6
  = let v7 = coe v0 v2 v3 v4 v5 v6 in
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
                                 (coe MAlonzo.Code.Untyped.Relation.C_inl_24 v10))
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v9)
                       (let v10 = coe v1 v2 v3 v4 v5 v6 in
                        coe
                          (case coe v10 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                               -> if coe v11
                                    then case coe v12 of
                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v13
                                             -> coe
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                  (coe v11)
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                     (coe
                                                        MAlonzo.Code.Untyped.Relation.C_inr_32 v13))
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
-- Untyped.Relation.Composable.empty?
d_empty'63'_396 ::
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
d_empty'63'_396 ~v0 ~v1 ~v2 ~v3 ~v4 = du_empty'63'_396
du_empty'63'_396 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_empty'63'_396
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
-- Untyped.Relation.Composable.Mu-dec
d_Mu'45'dec_406 ::
  ((Integer ->
    MAlonzo.Code.Untyped.T__'8866'_14 ->
    MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
   Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  ((Integer ->
    MAlonzo.Code.Untyped.T__'8866'_14 ->
    MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
   (Integer ->
    MAlonzo.Code.Untyped.T__'8866'_14 ->
    MAlonzo.Code.Untyped.T__'8866'_14 ->
    MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
   Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_Mu'45'dec_406 ~v0 v1 v2 v3 v4 = du_Mu'45'dec_406 v1 v2 v3 v4
du_Mu'45'dec_406 ::
  ((Integer ->
    MAlonzo.Code.Untyped.T__'8866'_14 ->
    MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
   (Integer ->
    MAlonzo.Code.Untyped.T__'8866'_14 ->
    MAlonzo.Code.Untyped.T__'8866'_14 ->
    MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
   Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_Mu'45'dec_406 v0 v1 v2 v3
  = let v4
          = coe v0 erased (coe du_Mu'45'dec_406 (coe v0)) v1 v2 v3 in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v7
                         -> coe
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                              (coe v5)
                              (coe
                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                 (coe MAlonzo.Code.Untyped.Relation.C_fix_46 v7))
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v6)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                          (coe v5)
                          (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Untyped.Relation.Composable..extendedlambda1
d_'46'extendedlambda1_434 ::
  ((Integer ->
    MAlonzo.Code.Untyped.T__'8866'_14 ->
    MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
   Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  ((Integer ->
    MAlonzo.Code.Untyped.T__'8866'_14 ->
    MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
   (Integer ->
    MAlonzo.Code.Untyped.T__'8866'_14 ->
    MAlonzo.Code.Untyped.T__'8866'_14 ->
    MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
   Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Untyped.Relation.T_Mu_36 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda1_434 = erased
-- Untyped.Relation.Composable.compatVar?
d_compatVar'63'_438 ::
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
d_compatVar'63'_438 ~v0 ~v1 ~v2 v3 v4 = du_compatVar'63'_438 v3 v4
du_compatVar'63'_438 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_compatVar'63'_438 v0 v1
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
                                                                         (coe C_'96'F__16)))
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
                                                                                                     C_'96'F__16)))
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
                                                                                                     C_'96'F__16)))
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
                                                                                                                              C_'96'F__16)))
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
-- Untyped.Relation.Composable.compatApply?
d_compatApply'63'_492 ::
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
d_compatApply'63'_492 ~v0 v1 v2 v3 v4
  = du_compatApply'63'_492 v1 v2 v3 v4
du_compatApply'63'_492 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_compatApply'63'_492 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
              (coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du__'183''63'__1230
                 (\ v4 ->
                    coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)
                 (\ v4 ->
                    coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)
                 (coe v2))
              (coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du__'183''63'__1230
                 (\ v4 ->
                    coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)
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
                                     MAlonzo.Code.VerifiedCompilation.UntypedViews.C__'183''33'__894 v12 v13
                                       -> case coe v2 of
                                            MAlonzo.Code.Untyped.C__'183'__22 v14 v15
                                              -> coe
                                                   seq (coe v12)
                                                   (coe
                                                      seq (coe v13)
                                                      (case coe v9 of
                                                         MAlonzo.Code.VerifiedCompilation.UntypedViews.C__'183''33'__894 v18 v19
                                                           -> case coe v3 of
                                                                MAlonzo.Code.Untyped.C__'183'__22 v20 v21
                                                                  -> coe
                                                                       seq (coe v18)
                                                                       (coe
                                                                          seq (coe v19)
                                                                          (let v22
                                                                                 = coe
                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                                                                                     (coe
                                                                                        v0 v1 v14
                                                                                        v20)
                                                                                     (coe
                                                                                        v0 v1 v15
                                                                                        v21) in
                                                                           coe
                                                                             (case coe v22 of
                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v23 v24
                                                                                  -> if coe v23
                                                                                       then case coe
                                                                                                   v24 of
                                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v25
                                                                                                -> case coe
                                                                                                          v25 of
                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                                                                       -> coe
                                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                            (coe
                                                                                                               v23)
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                               (coe
                                                                                                                  C__'183'F__48
                                                                                                                  v26
                                                                                                                  v27))
                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                       else coe
                                                                                              seq
                                                                                              (coe
                                                                                                 v24)
                                                                                              (coe
                                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                 (coe
                                                                                                    v23)
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
                       seq (coe v6)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                          (coe v5)
                          (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Untyped.Relation.Composable.compatLam?
d_compatLam'63'_572 ::
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
d_compatLam'63'_572 ~v0 v1 v2 v3 v4
  = du_compatLam'63'_572 v1 v2 v3 v4
du_compatLam'63'_572 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_compatLam'63'_572 v0 v1 v2 v3
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
                                                                               v0
                                                                               (addInt
                                                                                  (coe
                                                                                     (1 :: Integer))
                                                                                  (coe v1))
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
                                                                                                     C_ƛF_30
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
-- Untyped.Relation.Composable.compatForce?
d_compatForce'63'_636 ::
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
d_compatForce'63'_636 ~v0 v1 v2 v3 v4
  = du_compatForce'63'_636 v1 v2 v3 v4
du_compatForce'63'_636 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_compatForce'63'_636 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
              (coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du_force'63'_1344
                 (\ v4 ->
                    coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)
                 (coe v2))
              (coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du_force'63'_1344
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
                                     MAlonzo.Code.VerifiedCompilation.UntypedViews.C_force'33'_906 v11
                                       -> case coe v2 of
                                            MAlonzo.Code.Untyped.C_force_24 v12
                                              -> coe
                                                   seq (coe v11)
                                                   (case coe v9 of
                                                      MAlonzo.Code.VerifiedCompilation.UntypedViews.C_force'33'_906 v14
                                                        -> case coe v3 of
                                                             MAlonzo.Code.Untyped.C_force_24 v15
                                                               -> coe
                                                                    seq (coe v14)
                                                                    (let v16 = coe v0 v1 v12 v15 in
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
                                                                                                     C_forceF_62
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
-- Untyped.Relation.Composable.compatDelay?
d_compatDelay'63'_700 ::
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
d_compatDelay'63'_700 ~v0 v1 v2 v3 v4
  = du_compatDelay'63'_700 v1 v2 v3 v4
du_compatDelay'63'_700 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_compatDelay'63'_700 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
              (coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du_delay'63'_1422
                 (\ v4 ->
                    coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)
                 (coe v2))
              (coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du_delay'63'_1422
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
                                     MAlonzo.Code.VerifiedCompilation.UntypedViews.C_delay'33'_918 v11
                                       -> case coe v2 of
                                            MAlonzo.Code.Untyped.C_delay_26 v12
                                              -> coe
                                                   seq (coe v11)
                                                   (case coe v9 of
                                                      MAlonzo.Code.VerifiedCompilation.UntypedViews.C_delay'33'_918 v14
                                                        -> case coe v3 of
                                                             MAlonzo.Code.Untyped.C_delay_26 v15
                                                               -> coe
                                                                    seq (coe v14)
                                                                    (let v16 = coe v0 v1 v12 v15 in
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
                                                                                                     C_delayF_76
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
-- Untyped.Relation.Composable.pointwise?
d_pointwise'63'_772 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_pointwise'63'_772 ~v0 v1 v2 v3 v4
  = du_pointwise'63'_772 v1 v2 v3 v4
du_pointwise'63'_772 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_pointwise'63'_772 v0 v1 v2 v3
  = case coe v2 of
      []
        -> case coe v3 of
             []
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe MAlonzo.Code.Untyped.Relation.Pointwise.C_'91''93'_16))
             (:) v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      (:) v4 v5
        -> case coe v3 of
             []
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             (:) v6 v7
               -> let v8
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                            (coe v0 v1 v4 v6)
                            (coe du_pointwise'63'_772 (coe v0) (coe v1) (coe v5) (coe v7)) in
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
                                                      (coe
                                                         MAlonzo.Code.Untyped.Relation.Pointwise.C__'8759'__26
                                                         v12 v13))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              else coe
                                     seq (coe v10)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v9)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.Composable.compatConstr?
d_compatConstr'63'_826 ::
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
d_compatConstr'63'_826 ~v0 v1 v2 v3 v4
  = du_compatConstr'63'_826 v1 v2 v3 v4
du_compatConstr'63'_826 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_compatConstr'63'_826 v0 v1 v2 v3
  = let v4
          = \ v4 ->
              coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158 in
    coe
      (let v5
             = \ v5 ->
                 coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158 in
       coe
         (case coe v2 of
            MAlonzo.Code.Untyped.C_'96'_18 v6
              -> let v7 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                 coe
                   (coe
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                      (coe v7)
                      (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
            MAlonzo.Code.Untyped.C_ƛ_20 v6
              -> let v7 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                 coe
                   (coe
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                      (coe v7)
                      (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
            MAlonzo.Code.Untyped.C__'183'__22 v6 v7
              -> let v8 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                 coe
                   (coe
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                      (coe v8)
                      (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
            MAlonzo.Code.Untyped.C_force_24 v6
              -> let v7 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                 coe
                   (coe
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                      (coe v7)
                      (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
            MAlonzo.Code.Untyped.C_delay_26 v6
              -> let v7 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                 coe
                   (coe
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                      (coe v7)
                      (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
            MAlonzo.Code.Untyped.C_con_28 v6
              -> let v7 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                 coe
                   (coe
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                      (coe v7)
                      (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
            MAlonzo.Code.Untyped.C_constr_34 v6 v7
              -> let v8
                       = coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                           (coe v4 v6) (coe v5 v7) in
                 coe
                   (case coe v8 of
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                        -> if coe v9
                             then case coe v10 of
                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v11
                                      -> case coe v11 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                             -> coe
                                                  seq (coe v12)
                                                  (coe
                                                     seq (coe v13)
                                                     (case coe v3 of
                                                        MAlonzo.Code.Untyped.C_'96'_18 v14
                                                          -> let v15
                                                                   = coe
                                                                       MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                             coe
                                                               (coe
                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                  (coe v15)
                                                                  (coe
                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                        MAlonzo.Code.Untyped.C_ƛ_20 v14
                                                          -> let v15
                                                                   = coe
                                                                       MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                             coe
                                                               (coe
                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                  (coe v15)
                                                                  (coe
                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                        MAlonzo.Code.Untyped.C__'183'__22 v14 v15
                                                          -> let v16
                                                                   = coe
                                                                       MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                             coe
                                                               (coe
                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                  (coe v16)
                                                                  (coe
                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                        MAlonzo.Code.Untyped.C_force_24 v14
                                                          -> let v15
                                                                   = coe
                                                                       MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                             coe
                                                               (coe
                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                  (coe v15)
                                                                  (coe
                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                        MAlonzo.Code.Untyped.C_delay_26 v14
                                                          -> let v15
                                                                   = coe
                                                                       MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                             coe
                                                               (coe
                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                  (coe v15)
                                                                  (coe
                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                        MAlonzo.Code.Untyped.C_con_28 v14
                                                          -> let v15
                                                                   = coe
                                                                       MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                             coe
                                                               (coe
                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                  (coe v15)
                                                                  (coe
                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                        MAlonzo.Code.Untyped.C_constr_34 v14 v15
                                                          -> let v16
                                                                   = coe
                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                                                                       (coe
                                                                          MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796
                                                                          (coe v6) (coe v14))
                                                                       (coe
                                                                          MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158) in
                                                             coe
                                                               (case coe v16 of
                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                    -> if coe v17
                                                                         then case coe v18 of
                                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v19
                                                                                  -> case coe v19 of
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                                         -> coe
                                                                                              seq
                                                                                              (coe
                                                                                                 v21)
                                                                                              (let v22
                                                                                                     = coe
                                                                                                         du_pointwise'63'_772
                                                                                                         (coe
                                                                                                            v0)
                                                                                                         (coe
                                                                                                            v1)
                                                                                                         (coe
                                                                                                            v7)
                                                                                                         (coe
                                                                                                            v15) in
                                                                                               coe
                                                                                                 (case coe
                                                                                                         v22 of
                                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v23 v24
                                                                                                      -> if coe
                                                                                                              v23
                                                                                                           then case coe
                                                                                                                       v24 of
                                                                                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v25
                                                                                                                    -> coe
                                                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                         (coe
                                                                                                                            v23)
                                                                                                                         (coe
                                                                                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                                            (coe
                                                                                                                               C_constrF_104
                                                                                                                               v25))
                                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                           else coe
                                                                                                                  seq
                                                                                                                  (coe
                                                                                                                     v24)
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                     (coe
                                                                                                                        v23)
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                         else (let v19
                                                                                     = seq
                                                                                         (coe v18)
                                                                                         (coe
                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                            (coe
                                                                                               v17)
                                                                                            (coe
                                                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                                                               coe
                                                                                 (case coe v19 of
                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                                                      -> if coe v20
                                                                                           then case coe
                                                                                                       v21 of
                                                                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v22
                                                                                                    -> case coe
                                                                                                              v22 of
                                                                                                         MAlonzo.Code.VerifiedCompilation.UntypedViews.C_constr'33'_954 v25 v26
                                                                                                           -> coe
                                                                                                                seq
                                                                                                                (coe
                                                                                                                   v26)
                                                                                                                (let v27
                                                                                                                       = coe
                                                                                                                           du_pointwise'63'_772
                                                                                                                           (coe
                                                                                                                              v0)
                                                                                                                           (coe
                                                                                                                              v1)
                                                                                                                           (coe
                                                                                                                              v7)
                                                                                                                           (coe
                                                                                                                              v15) in
                                                                                                                 coe
                                                                                                                   (case coe
                                                                                                                           v27 of
                                                                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v28 v29
                                                                                                                        -> if coe
                                                                                                                                v28
                                                                                                                             then case coe
                                                                                                                                         v29 of
                                                                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v30
                                                                                                                                      -> coe
                                                                                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                                           (coe
                                                                                                                                              v28)
                                                                                                                                           (coe
                                                                                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                                                              (coe
                                                                                                                                                 C_constrF_104
                                                                                                                                                 v30))
                                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                             else coe
                                                                                                                                    seq
                                                                                                                                    (coe
                                                                                                                                       v29)
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                                       (coe
                                                                                                                                          v28)
                                                                                                                                       (coe
                                                                                                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                           else coe
                                                                                                  seq
                                                                                                  (coe
                                                                                                     v21)
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                     (coe
                                                                                                        v20)
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError))
                                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                                        MAlonzo.Code.Untyped.C_case_40 v14 v15
                                                          -> let v16
                                                                   = coe
                                                                       MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                             coe
                                                               (coe
                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                  (coe v16)
                                                                  (coe
                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                        MAlonzo.Code.Untyped.C_builtin_44 v14
                                                          -> let v15
                                                                   = coe
                                                                       MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                             coe
                                                               (coe
                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                  (coe v15)
                                                                  (coe
                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                        MAlonzo.Code.Untyped.C_error_46
                                                          -> let v14
                                                                   = coe
                                                                       MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                                                             coe
                                                               (coe
                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                  (coe v14)
                                                                  (coe
                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                        _ -> MAlonzo.RTE.mazUnreachableError))
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             else (let v11
                                         = seq
                                             (coe v10)
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                (coe v9)
                                                (coe
                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                   coe
                                     (case coe v11 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                          -> if coe v12
                                               then case coe v13 of
                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v14
                                                        -> case coe v14 of
                                                             MAlonzo.Code.VerifiedCompilation.UntypedViews.C_constr'33'_954 v17 v18
                                                               -> coe
                                                                    seq (coe v17)
                                                                    (coe
                                                                       seq (coe v18)
                                                                       (case coe v3 of
                                                                          MAlonzo.Code.Untyped.C_'96'_18 v19
                                                                            -> coe
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                 (coe v9)
                                                                                 (coe
                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                          MAlonzo.Code.Untyped.C_ƛ_20 v19
                                                                            -> coe
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                 (coe v9)
                                                                                 (coe
                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                          MAlonzo.Code.Untyped.C__'183'__22 v19 v20
                                                                            -> coe
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                 (coe v9)
                                                                                 (coe
                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                          MAlonzo.Code.Untyped.C_force_24 v19
                                                                            -> coe
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                 (coe v9)
                                                                                 (coe
                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                          MAlonzo.Code.Untyped.C_delay_26 v19
                                                                            -> coe
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                 (coe v9)
                                                                                 (coe
                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                          MAlonzo.Code.Untyped.C_con_28 v19
                                                                            -> coe
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                 (coe v9)
                                                                                 (coe
                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                          MAlonzo.Code.Untyped.C_constr_34 v19 v20
                                                                            -> let v21
                                                                                     = coe
                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                                                                                         (coe
                                                                                            MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796
                                                                                            (coe v6)
                                                                                            (coe
                                                                                               v19))
                                                                                         (coe
                                                                                            MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158) in
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
                                                                                                                seq
                                                                                                                (coe
                                                                                                                   v26)
                                                                                                                (let v27
                                                                                                                       = coe
                                                                                                                           du_pointwise'63'_772
                                                                                                                           (coe
                                                                                                                              v0)
                                                                                                                           (coe
                                                                                                                              v1)
                                                                                                                           (coe
                                                                                                                              v7)
                                                                                                                           (coe
                                                                                                                              v20) in
                                                                                                                 coe
                                                                                                                   (case coe
                                                                                                                           v27 of
                                                                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v28 v29
                                                                                                                        -> if coe
                                                                                                                                v28
                                                                                                                             then case coe
                                                                                                                                         v29 of
                                                                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v30
                                                                                                                                      -> coe
                                                                                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                                           (coe
                                                                                                                                              v28)
                                                                                                                                           (coe
                                                                                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                                                              (coe
                                                                                                                                                 C_constrF_104
                                                                                                                                                 v30))
                                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                             else coe
                                                                                                                                    seq
                                                                                                                                    (coe
                                                                                                                                       v29)
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                                       (coe
                                                                                                                                          v28)
                                                                                                                                       (coe
                                                                                                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                           else (let v24
                                                                                                       = seq
                                                                                                           (coe
                                                                                                              v23)
                                                                                                           (coe
                                                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                              (coe
                                                                                                                 v22)
                                                                                                              (coe
                                                                                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                                                                                 coe
                                                                                                   (case coe
                                                                                                           v24 of
                                                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v25 v26
                                                                                                        -> if coe
                                                                                                                v25
                                                                                                             then case coe
                                                                                                                         v26 of
                                                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v27
                                                                                                                      -> case coe
                                                                                                                                v27 of
                                                                                                                           MAlonzo.Code.VerifiedCompilation.UntypedViews.C_constr'33'_954 v30 v31
                                                                                                                             -> coe
                                                                                                                                  seq
                                                                                                                                  (coe
                                                                                                                                     v31)
                                                                                                                                  (let v32
                                                                                                                                         = coe
                                                                                                                                             du_pointwise'63'_772
                                                                                                                                             (coe
                                                                                                                                                v0)
                                                                                                                                             (coe
                                                                                                                                                v1)
                                                                                                                                             (coe
                                                                                                                                                v7)
                                                                                                                                             (coe
                                                                                                                                                v20) in
                                                                                                                                   coe
                                                                                                                                     (case coe
                                                                                                                                             v32 of
                                                                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v33 v34
                                                                                                                                          -> if coe
                                                                                                                                                  v33
                                                                                                                                               then case coe
                                                                                                                                                           v34 of
                                                                                                                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v35
                                                                                                                                                        -> coe
                                                                                                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                                                             (coe
                                                                                                                                                                v33)
                                                                                                                                                             (coe
                                                                                                                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                                                                                (coe
                                                                                                                                                                   C_constrF_104
                                                                                                                                                                   v35))
                                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                               else coe
                                                                                                                                                      seq
                                                                                                                                                      (coe
                                                                                                                                                         v34)
                                                                                                                                                      (coe
                                                                                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                                                         (coe
                                                                                                                                                            v33)
                                                                                                                                                         (coe
                                                                                                                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                             else coe
                                                                                                                    seq
                                                                                                                    (coe
                                                                                                                       v26)
                                                                                                                    (coe
                                                                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                       (coe
                                                                                                                          v25)
                                                                                                                       (coe
                                                                                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                                          MAlonzo.Code.Untyped.C_case_40 v19 v20
                                                                            -> coe
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                 (coe v9)
                                                                                 (coe
                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                          MAlonzo.Code.Untyped.C_builtin_44 v19
                                                                            -> coe
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                 (coe v9)
                                                                                 (coe
                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                          MAlonzo.Code.Untyped.C_error_46
                                                                            -> coe
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                 (coe v9)
                                                                                 (coe
                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                          _ -> MAlonzo.RTE.mazUnreachableError))
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               else coe
                                                      seq (coe v13)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                         (coe v12)
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                      _ -> MAlonzo.RTE.mazUnreachableError)
            MAlonzo.Code.Untyped.C_case_40 v6 v7
              -> let v8 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                 coe
                   (coe
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                      (coe v8)
                      (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
            MAlonzo.Code.Untyped.C_builtin_44 v6
              -> let v7 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                 coe
                   (coe
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                      (coe v7)
                      (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
            MAlonzo.Code.Untyped.C_error_46
              -> let v6 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                 coe
                   (coe
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                      (coe v6)
                      (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Untyped.Relation.Composable.compatCase?
d_compatCase'63'_924 ::
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
d_compatCase'63'_924 ~v0 v1 v2 v3 v4
  = du_compatCase'63'_924 v1 v2 v3 v4
du_compatCase'63'_924 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_compatCase'63'_924 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
              (coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du_case'63'_1502
                 (\ v4 ->
                    coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)
                 (\ v4 ->
                    coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)
                 (coe v2))
              (coe
                 MAlonzo.Code.VerifiedCompilation.UntypedViews.du_case'63'_1502
                 (\ v4 ->
                    coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)
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
                                     MAlonzo.Code.VerifiedCompilation.UntypedViews.C_case'33'_936 v12 v13
                                       -> case coe v2 of
                                            MAlonzo.Code.Untyped.C_case_40 v14 v15
                                              -> coe
                                                   seq (coe v12)
                                                   (coe
                                                      seq (coe v13)
                                                      (case coe v9 of
                                                         MAlonzo.Code.VerifiedCompilation.UntypedViews.C_case'33'_936 v18 v19
                                                           -> case coe v3 of
                                                                MAlonzo.Code.Untyped.C_case_40 v20 v21
                                                                  -> coe
                                                                       seq (coe v18)
                                                                       (coe
                                                                          seq (coe v19)
                                                                          (let v22
                                                                                 = coe
                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                                                                                     (coe
                                                                                        v0 v1 v14
                                                                                        v20)
                                                                                     (coe
                                                                                        du_pointwise'63'_772
                                                                                        (coe v0)
                                                                                        (coe v1)
                                                                                        (coe v15)
                                                                                        (coe
                                                                                           v21)) in
                                                                           coe
                                                                             (case coe v22 of
                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v23 v24
                                                                                  -> if coe v23
                                                                                       then case coe
                                                                                                   v24 of
                                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v25
                                                                                                -> case coe
                                                                                                          v25 of
                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                                                                       -> coe
                                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                            (coe
                                                                                                               v23)
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                               (coe
                                                                                                                  C_caseF_122
                                                                                                                  v26
                                                                                                                  v27))
                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                       else coe
                                                                                              seq
                                                                                              (coe
                                                                                                 v24)
                                                                                              (coe
                                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                 (coe
                                                                                                    v23)
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
                       seq (coe v6)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                          (coe v5)
                          (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Untyped.Relation.Composable.compatCon?
d_compatCon'63'_1004 ::
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
d_compatCon'63'_1004 ~v0 ~v1 ~v2 v3 v4
  = du_compatCon'63'_1004 v3 v4
du_compatCon'63'_1004 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_compatCon'63'_1004 v0 v1
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
                                                                         (coe C_conF_88)))
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
                                                                                                     C_conF_88)))
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
                                                                                                     C_conF_88)))
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
                                                                                                                              C_conF_88)))
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
-- Untyped.Relation.Composable.compatBuiltin?
d_compatBuiltin'63'_1058 ::
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
d_compatBuiltin'63'_1058 ~v0 ~v1 ~v2 v3 v4
  = du_compatBuiltin'63'_1058 v3 v4
du_compatBuiltin'63'_1058 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_compatBuiltin'63'_1058 v0 v1
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
                                                                         (coe C_builtinF_134)))
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
                                                                                                     C_builtinF_134)))
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
                                                                                                     C_builtinF_134)))
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
                                                                                                                              C_builtinF_134)))
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
-- Untyped.Relation.Composable.compatError?
d_compatError'63'_1112 ::
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
d_compatError'63'_1112 ~v0 ~v1 ~v2 v3 v4
  = du_compatError'63'_1112 v3 v4
du_compatError'63'_1112 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_compatError'63'_1112 v0 v1
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
                                              (coe C_errorF_144))))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v4)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                          (coe v3)
                          (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Untyped.Relation.Composable.compatTerm?
d_compatTerm'63'_1140 ::
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
d_compatTerm'63'_1140 ~v0 = du_compatTerm'63'_1140
du_compatTerm'63'_1140 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_compatTerm'63'_1140
  = coe
      du__'43''45'dec__318
      (\ v0 v1 v2 v3 v4 -> coe du_compatVar'63'_438 v3 v4)
      (coe
         du__'43''45'dec__318
         (\ v0 v1 v2 v3 v4 -> coe du_compatLam'63'_572 v1 v2 v3 v4)
         (coe
            du__'43''45'dec__318
            (\ v0 v1 v2 v3 v4 -> coe du_compatApply'63'_492 v1 v2 v3 v4)
            (coe
               du__'43''45'dec__318
               (\ v0 v1 v2 v3 v4 -> coe du_compatForce'63'_636 v1 v2 v3 v4)
               (coe
                  du__'43''45'dec__318
                  (\ v0 v1 v2 v3 v4 -> coe du_compatDelay'63'_700 v1 v2 v3 v4)
                  (coe
                     du__'43''45'dec__318
                     (\ v0 v1 v2 v3 v4 -> coe du_compatCon'63'_1004 v3 v4)
                     (coe
                        du__'43''45'dec__318
                        (\ v0 v1 v2 v3 v4 -> coe du_compatConstr'63'_826 v1 v2 v3 v4)
                        (coe
                           du__'43''45'dec__318
                           (\ v0 v1 v2 v3 v4 -> coe du_compatCase'63'_924 v1 v2 v3 v4)
                           (coe
                              du__'43''45'dec__318
                              (\ v0 v1 v2 v3 v4 -> coe du_compatBuiltin'63'_1058 v3 v4)
                              (coe
                                 du__'43''45'dec__318
                                 (\ v0 v1 v2 v3 v4 -> coe du_compatError'63'_1112 v3 v4)
                                 (\ v0 v1 v2 v3 v4 -> coe du_empty'63'_396))))))))))
      erased
