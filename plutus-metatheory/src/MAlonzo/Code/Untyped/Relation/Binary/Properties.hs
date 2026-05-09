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

module MAlonzo.Code.Untyped.Relation.Binary.Properties where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Untyped
import qualified MAlonzo.Code.Untyped.Relation.Binary.Core

-- Untyped.Relation.Binary.Properties.Reflexive
d_Reflexive_8 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  ()
d_Reflexive_8 = erased
-- Untyped.Relation.Binary.Properties.Transitive
d_Transitive_16 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  ()
d_Transitive_16 = erased
-- Untyped.Relation.Binary.Properties.Symmetric
d_Symmetric_28 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  ()
d_Symmetric_28 = erased
-- Untyped.Relation.Binary.Properties.Idempotent
d_Idempotent_38 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  ()
d_Idempotent_38 = erased
-- Untyped.Relation.Binary.Properties._⊆_
d__'8838'__50 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  ()
d__'8838'__50 = erased
-- Untyped.Relation.Binary.Properties.⊆-trans
d_'8838''45'trans_68 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny
d_'8838''45'trans_68 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_'8838''45'trans_68 v3 v4 v5 v6 v7 v8
du_'8838''45'trans_68 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny
du_'8838''45'trans_68 v0 v1 v2 v3 v4 v5
  = coe v1 v2 v3 v4 (coe v0 v2 v3 v4 v5)
-- Untyped.Relation.Binary.Properties.Transform
d_Transform_76 :: ()
d_Transform_76 = erased
-- Untyped.Relation.Binary.Properties.Transform?
d_Transform'63'_80 :: ()
d_Transform'63'_80 = erased
-- Untyped.Relation.Binary.Properties.Transform₂
d_Transform'8322'_84 :: ()
d_Transform'8322'_84 = erased
-- Untyped.Relation.Binary.Properties.Deterministicᵣ
d_Deterministic'7523'_88 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  ()
d_Deterministic'7523'_88 = erased
-- Untyped.Relation.Binary.Properties.Deterministicₗ
d_Deterministic'8343'_100 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  ()
d_Deterministic'8343'_100 = erased
-- Untyped.Relation.Binary.Properties.Compatible
d_Compatible_112 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  ()
d_Compatible_112 = erased
-- Untyped.Relation.Binary.Properties.Compatible₂
d_Compatible'8322'_124 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  ()
d_Compatible'8322'_124 = erased
-- Untyped.Relation.Binary.Properties.pointwise-refl
d_pointwise'45'refl_146 ::
  Integer ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  (Integer -> MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny) ->
  MAlonzo.Code.Untyped.Relation.Binary.Core.T_Pointwise_20
d_pointwise'45'refl_146 v0 ~v1 v2 v3
  = du_pointwise'45'refl_146 v0 v2 v3
du_pointwise'45'refl_146 ::
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  (Integer -> MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny) ->
  MAlonzo.Code.Untyped.Relation.Binary.Core.T_Pointwise_20
du_pointwise'45'refl_146 v0 v1 v2
  = case coe v1 of
      [] -> coe MAlonzo.Code.Untyped.Relation.Binary.Core.C_'91''93'_26
      (:) v3 v4
        -> coe
             MAlonzo.Code.Untyped.Relation.Binary.Core.C__'8759'__36
             (coe v2 v0 v3)
             (coe du_pointwise'45'refl_146 (coe v0) (coe v4) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.Binary.Properties.Refines
d_Refines_158 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  ()
d_Refines_158 = erased
-- Untyped.Relation.Binary.Properties.Refines?
d_Refines'63'_168 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   Maybe MAlonzo.Code.Untyped.T__'8866'_14) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  ()
d_Refines'63'_168 = erased
-- Untyped.Relation.Binary.Properties.Refines?-⊆
d_Refines'63''45''8838'_188 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   Maybe MAlonzo.Code.Untyped.T__'8866'_14) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_Refines'63''45''8838'_188 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_Refines'63''45''8838'_188 v3 v4 v5 v6 v7 v8
du_Refines'63''45''8838'_188 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_Refines'63''45''8838'_188 v0 v1 v2 v3 v4 v5
  = coe v0 v2 v3 v4 (coe v1 v2 v3 v4 v5)
-- Untyped.Relation.Binary.Properties.Refinement?
d_Refinement'63'_196 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  ()
d_Refinement'63'_196 = erased
-- Untyped.Relation.Binary.Properties.refine?
d_refine'63'_210 ::
  Integer ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Maybe MAlonzo.Code.Untyped.T__'8866'_14
d_refine'63'_210 v0 ~v1 v2 v3 = du_refine'63'_210 v0 v2 v3
du_refine'63'_210 ::
  Integer ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Maybe MAlonzo.Code.Untyped.T__'8866'_14
du_refine'63'_210 v0 v1 v2
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
-- Untyped.Relation.Binary.Properties.refine?-refines
d_refine'63''45'refines_234 ::
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
d_refine'63''45'refines_234 ~v0 v1 v2 v3 ~v4 ~v5
  = du_refine'63''45'refines_234 v1 v2 v3
du_refine'63''45'refines_234 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny
du_refine'63''45'refines_234 v0 v1 v2
  = let v3 = coe v0 v1 v2 in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6 -> coe v6
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
