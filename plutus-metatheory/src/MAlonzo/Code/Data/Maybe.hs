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

module MAlonzo.Code.Data.Maybe where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Maybe qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.Maybe.Relation.Unary.Any qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

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
         _                                            -> MAlonzo.RTE.mazUnreachableError)
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
      _                                            -> MAlonzo.RTE.mazUnreachableError
