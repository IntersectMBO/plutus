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

module MAlonzo.Code.Effect.Functor where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Level

-- Effect.Functor.RawFunctor
d_RawFunctor_24 a0 a1 a2 = ()
newtype T_RawFunctor_24
  = C_constructor_44 (() ->
                      () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny)
-- Effect.Functor.RawFunctor._<$>_
d__'60''36''62'__30 ::
  T_RawFunctor_24 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''36''62'__30 v0
  = case coe v0 of
      C_constructor_44 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Effect.Functor.RawFunctor._<$_
d__'60''36'__32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawFunctor_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''36'__32 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7
  = du__'60''36'__32 v3 v6 v7
du__'60''36'__32 ::
  T_RawFunctor_24 -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''36'__32 v0 v1 v2
  = coe d__'60''36''62'__30 v0 erased erased (\ v3 -> v1) v2
-- Effect.Functor.RawFunctor._<&>_
d__'60''38''62'__38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawFunctor_24 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'60''38''62'__38 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7
  = du__'60''38''62'__38 v3 v6 v7
du__'60''38''62'__38 ::
  T_RawFunctor_24 -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du__'60''38''62'__38 v0 v1 v2
  = coe d__'60''36''62'__30 v0 erased erased v2 v1
-- Effect.Functor.RawFunctor.ignore
d_ignore_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawFunctor_24 -> () -> AgdaAny -> AgdaAny
d_ignore_40 ~v0 ~v1 ~v2 v3 ~v4 = du_ignore_40 v3
du_ignore_40 :: T_RawFunctor_24 -> AgdaAny -> AgdaAny
du_ignore_40 v0
  = coe
      du__'60''36'__32 (coe v0)
      (coe
         MAlonzo.Code.Level.C_lift_20
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Effect.Functor.Morphism
d_Morphism_60 a0 a1 a2 a3 a4 a5 a6 = ()
newtype T_Morphism_60 = C_constructor_86 (() -> AgdaAny -> AgdaAny)
-- Effect.Functor.Morphism.op
d_op_78 :: T_Morphism_60 -> () -> AgdaAny -> AgdaAny
d_op_78 v0
  = case coe v0 of
      C_constructor_86 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Effect.Functor.Morphism.op-<$>
d_op'45''60''36''62'_84 ::
  T_Morphism_60 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_op'45''60''36''62'_84 = erased
