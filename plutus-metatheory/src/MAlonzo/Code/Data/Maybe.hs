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

module MAlonzo.Code.Data.Maybe where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Maybe.Relation.Unary.Any

-- Data.Maybe.Is-just
d_Is'45'just_8 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> Maybe AgdaAny -> ()
d_Is'45'just_8 = erased
-- Data.Maybe.Is-nothing
d_Is'45'nothing_12 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> Maybe AgdaAny -> ()
d_Is'45'nothing_12 = erased
-- Data.Maybe.to-witness
d_to'45'witness_18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Maybe AgdaAny ->
  MAlonzo.Code.Data.Maybe.Relation.Unary.Any.T_Any_18 -> AgdaAny
d_to'45'witness_18 ~v0 ~v1 v2 v3 = du_to'45'witness_18 v2 v3
du_to'45'witness_18 ::
  Maybe AgdaAny ->
  MAlonzo.Code.Data.Maybe.Relation.Unary.Any.T_Any_18 -> AgdaAny
du_to'45'witness_18 v0 v1
  = coe
      seq (coe v1)
      (case coe v0 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2 -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Maybe.to-witness-T
d_to'45'witness'45'T_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Maybe AgdaAny -> AgdaAny -> AgdaAny
d_to'45'witness'45'T_24 ~v0 ~v1 v2 ~v3
  = du_to'45'witness'45'T_24 v2
du_to'45'witness'45'T_24 :: Maybe AgdaAny -> AgdaAny
du_to'45'witness'45'T_24 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
