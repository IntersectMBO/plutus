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

module MAlonzo.Code.Data.Maybe.Relation.Binary.Connected where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Function.Bundles
import qualified MAlonzo.Code.Relation.Nullary.Decidable
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Data.Maybe.Relation.Binary.Connected.Connected
d_Connected_42 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_Connected_42
  = C_just_50 AgdaAny | C_just'45'nothing_52 | C_nothing'45'just_54 |
    C_nothing_56
-- Data.Maybe.Relation.Binary.Connected.drop-just
d_drop'45'just_58 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> AgdaAny -> T_Connected_42 -> AgdaAny
d_drop'45'just_58 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_drop'45'just_58 v8
du_drop'45'just_58 :: T_Connected_42 -> AgdaAny
du_drop'45'just_58 v0
  = case coe v0 of
      C_just_50 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Maybe.Relation.Binary.Connected.just-equivalence
d_just'45'equivalence_62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Function.Bundles.T_Equivalence_1810
d_just'45'equivalence_62 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_just'45'equivalence_62
du_just'45'equivalence_62 ::
  MAlonzo.Code.Function.Bundles.T_Equivalence_1810
du_just'45'equivalence_62
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8660'_2414 (coe C_just_50)
      (coe du_drop'45'just_58)
-- Data.Maybe.Relation.Binary.Connected.refl
d_refl_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> Maybe AgdaAny -> T_Connected_42
d_refl_64 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_refl_64 v4 v5
du_refl_64 ::
  (AgdaAny -> AgdaAny) -> Maybe AgdaAny -> T_Connected_42
du_refl_64 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe C_just_50 (coe v0 v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe C_nothing_56
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Maybe.Relation.Binary.Connected.reflexive
d_reflexive_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_Connected_42
d_reflexive_70 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7
  = du_reflexive_70 v4 v5
du_reflexive_70 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  Maybe AgdaAny -> T_Connected_42
du_reflexive_70 v0 v1
  = coe du_refl_64 (coe (\ v2 -> coe v0 v2 v2 erased)) (coe v1)
-- Data.Maybe.Relation.Binary.Connected.sym
d_sym_74 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny -> Maybe AgdaAny -> T_Connected_42 -> T_Connected_42
d_sym_74 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10 v11
  = du_sym_74 v8 v9 v10 v11
du_sym_74 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny -> Maybe AgdaAny -> T_Connected_42 -> T_Connected_42
du_sym_74 v0 v1 v2 v3
  = case coe v3 of
      C_just_50 v6
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                      -> coe C_just_50 (coe v0 v7 v8 v6)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_just'45'nothing_52 -> coe C_nothing'45'just_54
      C_nothing'45'just_54 -> coe C_just'45'nothing_52
      C_nothing_56 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Maybe.Relation.Binary.Connected.connected?
d_connected'63'_86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_connected'63'_86 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_connected'63'_86 v6 v7 v8
du_connected'63'_86 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_connected'63'_86 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.du_map_18
                    (coe du_just'45'equivalence_62) (coe v0 v3 v4)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe C_just'45'nothing_52))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe C_nothing'45'just_54))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe C_nothing_56))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
