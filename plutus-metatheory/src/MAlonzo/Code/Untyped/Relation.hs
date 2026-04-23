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

module MAlonzo.Code.Untyped.Relation where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Builtin
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.RawU
import qualified MAlonzo.Code.Untyped
import qualified MAlonzo.Code.Untyped.Relation.Pointwise

-- Untyped.Relation._+_
d__'43'__10 a0 a1 a2 a3 a4 a5 = ()
data T__'43'__10 = C_inl_24 AgdaAny | C_inr_32 AgdaAny
-- Untyped.Relation.Mu
d_Mu_36 a0 a1 a2 a3 = ()
newtype T_Mu_36 = C_fix_46 AgdaAny
-- Untyped.Relation.Empty
d_Empty_48 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> ()
d_Empty_48 = erased
-- Untyped.Relation.Const
d_Const_56 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> ()
d_Const_56 = erased
-- Untyped.Relation.Refinement?
d_Refinement'63'_60 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  ()
d_Refinement'63'_60 = erased
-- Untyped.Relation.refine?
d_refine'63'_74 ::
  Integer ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Maybe MAlonzo.Code.Untyped.T__'8866'_14
d_refine'63'_74 v0 ~v1 v2 v3 = du_refine'63'_74 v0 v2 v3
du_refine'63'_74 ::
  Integer ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Maybe MAlonzo.Code.Untyped.T__'8866'_14
du_refine'63'_74 v0 v1 v2
  = let v3 = coe v1 v0 v2 in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v5)
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Untyped.Relation.refine?-refines
d_refine'63''45'refines_98 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_refine'63''45'refines_98 ~v0 v1 v2 v3 ~v4 ~v5
  = du_refine'63''45'refines_98 v1 v2 v3
du_refine'63''45'refines_98 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny
du_refine'63''45'refines_98 v0 v1 v2
  = let v3 = coe v0 v1 v2 in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6 -> coe v6
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Untyped.Relation._<|>_
d__'60''124''62'__124 ::
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
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d__'60''124''62'__124 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du__'60''124''62'__124 v3 v4 v5 v6
du__'60''124''62'__124 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du__'60''124''62'__124 v0 v1 v2 v3
  = let v4 = coe v0 v2 v3 in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
           -> case coe v5 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                          (coe C_inl_24 v7))
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> let v5 = coe v1 v2 v3 in
              coe
                (case coe v5 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                     -> case coe v6 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                                    (coe C_inr_32 v8))
                          _ -> MAlonzo.RTE.mazUnreachableError
                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Untyped.Relation.Equivalence
d_Equivalence_174 a0 = ()
data T_Equivalence_174
  = C_constructor_190 (Integer ->
                       MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny)
                      (Integer ->
                       MAlonzo.Code.Untyped.T__'8866'_14 ->
                       MAlonzo.Code.Untyped.T__'8866'_14 ->
                       MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny -> AgdaAny)
                      (Integer ->
                       MAlonzo.Code.Untyped.T__'8866'_14 ->
                       MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny)
-- Untyped.Relation.Equivalence.~-refl
d_'126''45'refl_184 ::
  T_Equivalence_174 ->
  Integer -> MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny
d_'126''45'refl_184 v0
  = case coe v0 of
      C_constructor_190 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.Equivalence.~-trans
d_'126''45'trans_186 ::
  T_Equivalence_174 ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny -> AgdaAny
d_'126''45'trans_186 v0
  = case coe v0 of
      C_constructor_190 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.Equivalence.~-sym
d_'126''45'sym_188 ::
  T_Equivalence_174 ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny
d_'126''45'sym_188 v0
  = case coe v0 of
      C_constructor_190 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.TermCompatible
d_TermCompatible_194 a0 = ()
data T_TermCompatible_194
  = C_constructor_314 (Integer ->
                       MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny)
                      (Integer ->
                       MAlonzo.Code.Untyped.T__'8866'_14 ->
                       MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny)
                      (Integer ->
                       MAlonzo.Code.Untyped.T__'8866'_14 ->
                       MAlonzo.Code.Untyped.T__'8866'_14 ->
                       MAlonzo.Code.Untyped.T__'8866'_14 ->
                       MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny -> AgdaAny)
                      (Integer ->
                       MAlonzo.Code.Untyped.T__'8866'_14 ->
                       MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny)
                      (Integer ->
                       MAlonzo.Code.Untyped.T__'8866'_14 ->
                       MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny)
                      (Integer ->
                       Integer ->
                       [MAlonzo.Code.Untyped.T__'8866'_14] ->
                       [MAlonzo.Code.Untyped.T__'8866'_14] ->
                       MAlonzo.Code.Untyped.Relation.Pointwise.T_Pointwise_10 -> AgdaAny)
                      (Integer ->
                       MAlonzo.Code.Untyped.T__'8866'_14 ->
                       MAlonzo.Code.Untyped.T__'8866'_14 ->
                       [MAlonzo.Code.Untyped.T__'8866'_14] ->
                       [MAlonzo.Code.Untyped.T__'8866'_14] ->
                       AgdaAny ->
                       MAlonzo.Code.Untyped.Relation.Pointwise.T_Pointwise_10 -> AgdaAny)
                      (MAlonzo.Code.RawU.T_TmCon_202 -> Integer -> AgdaAny)
                      (Integer -> MAlonzo.Code.Builtin.T_Builtin_2 -> AgdaAny)
                      (Integer -> AgdaAny)
-- Untyped.Relation.TermCompatible.compat-var
d_compat'45'var_260 ::
  T_TermCompatible_194 ->
  Integer -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d_compat'45'var_260 v0
  = case coe v0 of
      C_constructor_314 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.TermCompatible.compat-ƛ
d_compat'45'ƛ_268 ::
  T_TermCompatible_194 ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny
d_compat'45'ƛ_268 v0
  = case coe v0 of
      C_constructor_314 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.TermCompatible.compat-·
d_compat'45''183'_270 ::
  T_TermCompatible_194 ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny -> AgdaAny
d_compat'45''183'_270 v0
  = case coe v0 of
      C_constructor_314 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.TermCompatible.compat-force
d_compat'45'force_272 ::
  T_TermCompatible_194 ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny
d_compat'45'force_272 v0
  = case coe v0 of
      C_constructor_314 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.TermCompatible.compat-delay
d_compat'45'delay_274 ::
  T_TermCompatible_194 ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny
d_compat'45'delay_274 v0
  = case coe v0 of
      C_constructor_314 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.TermCompatible.compat-constr
d_compat'45'constr_284 ::
  T_TermCompatible_194 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Untyped.Relation.Pointwise.T_Pointwise_10 -> AgdaAny
d_compat'45'constr_284 v0
  = case coe v0 of
      C_constructor_314 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.TermCompatible.compat-case
d_compat'45'case_296 ::
  T_TermCompatible_194 ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  AgdaAny ->
  MAlonzo.Code.Untyped.Relation.Pointwise.T_Pointwise_10 -> AgdaAny
d_compat'45'case_296 v0
  = case coe v0 of
      C_constructor_314 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.TermCompatible.compat-con
d_compat'45'con_302 ::
  T_TermCompatible_194 ->
  MAlonzo.Code.RawU.T_TmCon_202 -> Integer -> AgdaAny
d_compat'45'con_302 v0
  = case coe v0 of
      C_constructor_314 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.TermCompatible.compat-builtin
d_compat'45'builtin_308 ::
  T_TermCompatible_194 ->
  Integer -> MAlonzo.Code.Builtin.T_Builtin_2 -> AgdaAny
d_compat'45'builtin_308 v0
  = case coe v0 of
      C_constructor_314 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.TermCompatible.compat-error
d_compat'45'error_312 :: T_TermCompatible_194 -> Integer -> AgdaAny
d_compat'45'error_312 v0
  = case coe v0 of
      C_constructor_314 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
