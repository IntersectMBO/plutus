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

module MAlonzo.Code.Data.These where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.These.Base
import qualified MAlonzo.Code.Function.Base

-- Data.These.fromThis
d_fromThis_12 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Data.These.Base.T_These_38 -> Maybe AgdaAny
d_fromThis_12 ~v0 ~v1 ~v2 ~v3 = du_fromThis_12
du_fromThis_12 ::
  MAlonzo.Code.Data.These.Base.T_These_38 -> Maybe AgdaAny
du_fromThis_12
  = coe
      MAlonzo.Code.Data.These.Base.du_fold_92
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16)
      (let v0 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
       coe (coe (\ v1 -> v0)))
      (coe
         MAlonzo.Code.Function.Base.du__'8728''8242'__216
         (coe (\ v0 v1 -> v0))
         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16))
-- Data.These.fromThat
d_fromThat_14 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Data.These.Base.T_These_38 -> Maybe AgdaAny
d_fromThat_14 ~v0 ~v1 ~v2 ~v3 = du_fromThat_14
du_fromThat_14 ::
  MAlonzo.Code.Data.These.Base.T_These_38 -> Maybe AgdaAny
du_fromThat_14
  = coe
      MAlonzo.Code.Data.These.Base.du_fold_92
      (let v0 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
       coe (coe (\ v1 -> v0)))
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16)
      (let v0 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 in
       coe (coe (\ v1 -> v0)))
-- Data.These.leftMost
d_leftMost_16 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Data.These.Base.T_These_38 -> AgdaAny
d_leftMost_16 ~v0 ~v1 = du_leftMost_16
du_leftMost_16 ::
  MAlonzo.Code.Data.These.Base.T_These_38 -> AgdaAny
du_leftMost_16
  = coe
      MAlonzo.Code.Data.These.Base.du_fold_92 (coe (\ v0 -> v0))
      (coe (\ v0 -> v0)) (coe (\ v0 v1 -> v0))
-- Data.These.rightMost
d_rightMost_18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Data.These.Base.T_These_38 -> AgdaAny
d_rightMost_18 ~v0 ~v1 = du_rightMost_18
du_rightMost_18 ::
  MAlonzo.Code.Data.These.Base.T_These_38 -> AgdaAny
du_rightMost_18
  = coe
      MAlonzo.Code.Data.These.Base.du_fold_92 (coe (\ v0 -> v0))
      (coe (\ v0 -> v0)) (coe (\ v0 v1 -> v1))
-- Data.These.mergeThese
d_mergeThese_20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.These.Base.T_These_38 -> AgdaAny
d_mergeThese_20 ~v0 ~v1 = du_mergeThese_20
du_mergeThese_20 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.These.Base.T_These_38 -> AgdaAny
du_mergeThese_20
  = coe
      MAlonzo.Code.Data.These.Base.du_fold_92 (coe (\ v0 -> v0))
      (coe (\ v0 -> v0))
-- Data.These.deleteThis
d_deleteThis_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.These.Base.T_These_38 ->
  Maybe MAlonzo.Code.Data.These.Base.T_These_38
d_deleteThis_22 ~v0 ~v1 ~v2 ~v3 = du_deleteThis_22
du_deleteThis_22 ::
  MAlonzo.Code.Data.These.Base.T_These_38 ->
  Maybe MAlonzo.Code.Data.These.Base.T_These_38
du_deleteThis_22
  = coe
      MAlonzo.Code.Data.These.Base.du_fold_92
      (let v0 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
       coe (coe (\ v1 -> v0)))
      (coe
         MAlonzo.Code.Function.Base.du__'8728''8242'__216
         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16)
         (coe MAlonzo.Code.Data.These.Base.C_that_50))
      (let v0
             = coe
                 MAlonzo.Code.Function.Base.du__'8728''8242'__216
                 (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16)
                 (coe MAlonzo.Code.Data.These.Base.C_that_50) in
       coe (coe (\ v1 -> v0)))
-- Data.These.deleteThat
d_deleteThat_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.These.Base.T_These_38 ->
  Maybe MAlonzo.Code.Data.These.Base.T_These_38
d_deleteThat_24 ~v0 ~v1 ~v2 ~v3 = du_deleteThat_24
du_deleteThat_24 ::
  MAlonzo.Code.Data.These.Base.T_These_38 ->
  Maybe MAlonzo.Code.Data.These.Base.T_These_38
du_deleteThat_24
  = coe
      MAlonzo.Code.Data.These.Base.du_fold_92
      (coe
         MAlonzo.Code.Function.Base.du__'8728''8242'__216
         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16)
         (coe MAlonzo.Code.Data.These.Base.C_this_48))
      (let v0 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
       coe (coe (\ v1 -> v0)))
      (coe
         MAlonzo.Code.Function.Base.du__'8728''8242'__216
         (coe (\ v0 v1 -> v0))
         (coe
            MAlonzo.Code.Function.Base.du__'8728''8242'__216
            (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16)
            (coe MAlonzo.Code.Data.These.Base.C_this_48)))
