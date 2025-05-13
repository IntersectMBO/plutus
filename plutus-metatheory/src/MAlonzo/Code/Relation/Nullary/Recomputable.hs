{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE EmptyCase                 #-}
{-# LANGUAGE EmptyDataDecls            #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE PatternSynonyms           #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module MAlonzo.Code.Relation.Nullary.Recomputable where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.Irrelevant qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Relation.Nullary.Recomputable.Recomputable
d_Recomputable_16 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()
d_Recomputable_16 = erased
-- Relation.Nullary.Recomputable.recompute-constant
d_recompute'45'constant_26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_recompute'45'constant_26 = erased
-- Relation.Nullary.Recomputable.⊥-recompute
d_'8869''45'recompute_34 ::
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8869''45'recompute_34 = erased
-- Relation.Nullary.Recomputable._×-recompute_
d__'215''45'recompute__36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d__'215''45'recompute__36 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6
  = du__'215''45'recompute__36 v4 v5
du__'215''45'recompute__36 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du__'215''45'recompute__36 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0 erased)
      (coe v1 erased)
-- Relation.Nullary.Recomputable._→-recompute_
d__'8594''45'recompute__46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'8594''45'recompute__46 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6
  = du__'8594''45'recompute__46 v4
du__'8594''45'recompute__46 :: (AgdaAny -> AgdaAny) -> AgdaAny
du__'8594''45'recompute__46 v0 = coe v0 erased
-- Relation.Nullary.Recomputable.Π-recompute
d_Π'45'recompute_62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_Π'45'recompute_62 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6
  = du_Π'45'recompute_62 v4 v6
du_Π'45'recompute_62 ::
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_Π'45'recompute_62 v0 v1 = coe v0 v1 erased
-- Relation.Nullary.Recomputable.∀-recompute
d_'8704''45'recompute_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8704''45'recompute_78 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6
  = du_'8704''45'recompute_78 v4 v6
du_'8704''45'recompute_78 ::
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_'8704''45'recompute_78 v0 v1 = coe v0 v1 erased
-- Relation.Nullary.Recomputable.¬-recompute
d_'172''45'recompute_86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'172''45'recompute_86 = erased
