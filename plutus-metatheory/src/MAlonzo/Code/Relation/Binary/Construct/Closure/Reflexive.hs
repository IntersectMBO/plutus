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

module MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive

-- Relation.Binary.Construct.Closure.Reflexive.ReflClosure
d_ReflClosure_30 a0 a1 a2 a3 a4 a5 = ()
data T_ReflClosure_30 = C_refl_36 | C_'91'_'93'_44 AgdaAny
-- Relation.Binary.Construct.Closure.Reflexive.map
d_map_52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_ReflClosure_30 -> T_ReflClosure_30
d_map_52 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 v11 v12
  = du_map_52 v9 v10 v11 v12
du_map_52 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_ReflClosure_30 -> T_ReflClosure_30
du_map_52 v0 v1 v2 v3
  = case coe v3 of
      C_refl_36 -> coe C_refl_36
      C_'91'_'93'_44 v6 -> coe C_'91'_'93'_44 (coe v0 v1 v2 v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Closure.Reflexive.drop-refl
d_drop'45'refl_62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_ReflClosure_30 -> AgdaAny
d_drop'45'refl_62 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 v7
  = du_drop'45'refl_62 v4 v5 v7
du_drop'45'refl_62 ::
  (AgdaAny -> AgdaAny) -> AgdaAny -> T_ReflClosure_30 -> AgdaAny
du_drop'45'refl_62 v0 v1 v2
  = case coe v2 of
      C_refl_36 -> coe v0 v1
      C_'91'_'93'_44 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Closure.Reflexive.reflexive
d_reflexive_72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_ReflClosure_30
d_reflexive_72 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_reflexive_72
du_reflexive_72 :: T_ReflClosure_30
du_reflexive_72 = coe C_refl_36
-- Relation.Binary.Construct.Closure.Reflexive.[]-injective
d_'91''93''45'injective_84 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'91''93''45'injective_84 = erased
-- Relation.Binary.Construct.Closure.Reflexive.Refl
d_Refl_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny -> ()) -> AgdaAny -> AgdaAny -> ()
d_Refl_96 = erased
