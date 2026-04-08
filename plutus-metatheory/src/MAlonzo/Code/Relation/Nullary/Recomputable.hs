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

module MAlonzo.Code.Relation.Nullary.Recomputable where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Irrelevant

-- Relation.Nullary.Recomputable.irrelevant-recompute
d_irrelevant'45'recompute_14 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irrelevant'45'recompute_14 = erased
-- Relation.Nullary.Recomputable.⊥-recompute
d_'8869''45'recompute_18 ::
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8869''45'recompute_18 = erased
-- Relation.Nullary.Recomputable._×-recompute_
d__'215''45'recompute__20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d__'215''45'recompute__20 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6
  = du__'215''45'recompute__20 v4 v5
du__'215''45'recompute__20 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du__'215''45'recompute__20 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0 erased)
      (coe v1 erased)
-- Relation.Nullary.Recomputable._→-recompute_
d__'8594''45'recompute__30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'8594''45'recompute__30 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6
  = du__'8594''45'recompute__30 v4
du__'8594''45'recompute__30 :: (AgdaAny -> AgdaAny) -> AgdaAny
du__'8594''45'recompute__30 v0 = coe v0 erased
-- Relation.Nullary.Recomputable.Π-recompute
d_Π'45'recompute_46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_Π'45'recompute_46 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6
  = du_Π'45'recompute_46 v4 v6
du_Π'45'recompute_46 ::
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_Π'45'recompute_46 v0 v1 = coe v0 v1 erased
-- Relation.Nullary.Recomputable.∀-recompute
d_'8704''45'recompute_62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8704''45'recompute_62 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6
  = du_'8704''45'recompute_62 v4 v6
du_'8704''45'recompute_62 ::
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_'8704''45'recompute_62 v0 v1 = coe v0 v1 erased
-- Relation.Nullary.Recomputable.¬-recompute
d_'172''45'recompute_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'172''45'recompute_70 = erased
