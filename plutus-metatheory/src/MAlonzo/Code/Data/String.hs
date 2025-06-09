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

module MAlonzo.Code.Data.String where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Char qualified
import MAlonzo.Code.Agda.Builtin.String qualified
import MAlonzo.Code.Data.Bool.Base qualified
import MAlonzo.Code.Data.Char.Properties qualified
import MAlonzo.Code.Data.List.Base qualified
import MAlonzo.Code.Data.List.Extrema qualified
import MAlonzo.Code.Data.List.Membership.DecSetoid qualified
import MAlonzo.Code.Data.Nat.Properties qualified
import MAlonzo.Code.Data.String.Base qualified
import MAlonzo.Code.Data.Vec.Base qualified
import MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties qualified
import MAlonzo.Code.Relation.Nullary.Decidable.Core qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.String.toVec
d_toVec_122 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_toVec_122 v0
  = coe
      MAlonzo.Code.Data.Vec.Base.du_fromList_600
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)
-- Data.String.fromVec
d_fromVec_128 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_fromVec_128 ~v0 v1 = du_fromVec_128 v1
du_fromVec_128 ::
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_fromVec_128 v0
  = coe
      MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14
      (coe MAlonzo.Code.Data.Vec.Base.du_toList_592 (coe v0))
-- Data.String.parensIfSpace
d_parensIfSpace_130 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_parensIfSpace_130 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe
         MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
         (coe
            MAlonzo.Code.Data.List.Membership.DecSetoid.du__'8712''63'__58
            (coe
               MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
               (coe MAlonzo.Code.Data.Char.Properties.d__'8799'__14))
            (coe ' ')
            (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)))
      (coe MAlonzo.Code.Data.String.Base.d_parens_46 v0) (coe v0)
-- Data.String.rectangle
d_rectangle_136 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_rectangle_136 ~v0 v1 v2 = du_rectangle_136 v1 v2
du_rectangle_136 ::
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
du_rectangle_136 v0 v1
  = coe
      MAlonzo.Code.Data.Vec.Base.du_zipWith_242
      (coe (\ v2 -> coe v2 (coe du_width_148 (coe v1)))) (coe v0)
      (coe v1)
-- Data.String._.sizes
d_sizes_146 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> [Integer]
d_sizes_146 ~v0 ~v1 v2 = du_sizes_146 v2
du_sizes_146 :: MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> [Integer]
du_sizes_146 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_map_22
      (coe MAlonzo.Code.Data.String.Base.d_length_22)
      (coe MAlonzo.Code.Data.Vec.Base.du_toList_592 (coe v0))
-- Data.String._.width
d_width_148 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
d_width_148 ~v0 ~v1 v2 = du_width_148 v2
du_width_148 :: MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
du_width_148 v0
  = coe
      MAlonzo.Code.Data.List.Extrema.du_max_142
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2826
      (0 :: Integer) (coe du_sizes_146 (coe v0))
-- Data.String.rectangleˡ
d_rectangle'737'_156 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_rectangle'737'_156 v0 v1
  = coe
      du_rectangle_136
      (coe
         MAlonzo.Code.Data.Vec.Base.du_replicate_444 (coe v0)
         (coe MAlonzo.Code.Data.String.Base.d_padLeft_60 (coe v1)))
-- Data.String.rectangleʳ
d_rectangle'691'_162 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_rectangle'691'_162 v0 v1
  = coe
      du_rectangle_136
      (coe
         MAlonzo.Code.Data.Vec.Base.du_replicate_444 (coe v0)
         (coe MAlonzo.Code.Data.String.Base.d_padRight_70 (coe v1)))
-- Data.String.rectangleᶜ
d_rectangle'7580'_168 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_rectangle'7580'_168 v0 v1 v2
  = coe
      du_rectangle_136
      (coe
         MAlonzo.Code.Data.Vec.Base.du_replicate_444 (coe v0)
         (coe MAlonzo.Code.Data.String.Base.d_padBoth_80 (coe v1) (coe v2)))
