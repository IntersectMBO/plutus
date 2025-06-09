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

module MAlonzo.Code.Data.Vec.Bounded.Base where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.Nat qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.List.Base qualified
import MAlonzo.Code.Data.List.Extrema qualified
import MAlonzo.Code.Data.List.Membership.Setoid qualified
import MAlonzo.Code.Data.List.Relation.Unary.All qualified
import MAlonzo.Code.Data.List.Relation.Unary.All.Properties qualified
import MAlonzo.Code.Data.Nat.Base qualified
import MAlonzo.Code.Data.Nat.Properties qualified
import MAlonzo.Code.Data.These.Base qualified
import MAlonzo.Code.Data.Vec.Base qualified
import MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties qualified
import MAlonzo.Code.Relation.Nullary.Decidable.Core qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.Vec.Bounded.Base.Vec≤
d_Vec'8804'_126 a0 a1 a2 = ()
data T_Vec'8804'_126
  = C__'44'__144 Integer MAlonzo.Code.Data.Vec.Base.T_Vec_28
-- Data.Vec.Bounded.Base.Vec≤.length
d_length_138 :: T_Vec'8804'_126 -> Integer
d_length_138 v0
  = case coe v0 of
      C__'44'__144 v1 v2 -> coe v1
      _                  -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Bounded.Base.Vec≤.vec
d_vec_140 :: T_Vec'8804'_126 -> MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_vec_140 v0
  = case coe v0 of
      C__'44'__144 v1 v2 -> coe v2
      _                  -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Bounded.Base.isBounded
d_isBounded_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  T_Vec'8804'_126 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_isBounded_148 ~v0 ~v1 v2 v3 = du_isBounded_148 v2 v3
du_isBounded_148 ::
  Integer ->
  T_Vec'8804'_126 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_isBounded_148 v0 v1
  = case coe v1 of
      C__'44'__144 v2 v3
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.du_recompute_54
             (MAlonzo.Code.Data.Nat.Properties.d__'8804''63'__2802
                (coe v2) (coe v0))
             erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Bounded.Base.toVec
d_toVec_156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer -> T_Vec'8804'_126 -> MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_toVec_156 ~v0 ~v1 ~v2 v3 = du_toVec_156 v3
du_toVec_156 ::
  T_Vec'8804'_126 -> MAlonzo.Code.Data.Vec.Base.T_Vec_28
du_toVec_156 v0
  = case coe v0 of
      C__'44'__144 v1 v2 -> coe v2
      _                  -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Bounded.Base.fromVec
d_fromVec_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> T_Vec'8804'_126
d_fromVec_162 ~v0 ~v1 v2 v3 = du_fromVec_162 v2 v3
du_fromVec_162 ::
  Integer -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> T_Vec'8804'_126
du_fromVec_162 v0 v1 = coe C__'44'__144 v0 v1
-- Data.Vec.Bounded.Base.padRight
d_padRight_166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  AgdaAny -> T_Vec'8804'_126 -> MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_padRight_166 ~v0 ~v1 v2 v3 v4 = du_padRight_166 v2 v3 v4
du_padRight_166 ::
  Integer ->
  AgdaAny -> T_Vec'8804'_126 -> MAlonzo.Code.Data.Vec.Base.T_Vec_28
du_padRight_166 v0 v1 v2
  = case coe v2 of
      C__'44'__144 v3 v4
        -> let v6 = coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v0 v3 in
           coe
             (coe
                MAlonzo.Code.Data.Vec.Base.du__'43''43'__188 (coe v4)
                (coe
                   MAlonzo.Code.Data.Vec.Base.du_replicate_444 (coe v6) (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Bounded.Base.padLeft
d_padLeft_182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  AgdaAny -> T_Vec'8804'_126 -> MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_padLeft_182 ~v0 ~v1 v2 v3 v4 = du_padLeft_182 v2 v3 v4
du_padLeft_182 ::
  Integer ->
  AgdaAny -> T_Vec'8804'_126 -> MAlonzo.Code.Data.Vec.Base.T_Vec_28
du_padLeft_182 v0 v1 v2
  = case coe v2 of
      C__'44'__144 v3 v4
        -> let v6 = coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v0 v3 in
           coe
             (coe
                MAlonzo.Code.Data.Vec.Base.du__'43''43'__188
                (coe MAlonzo.Code.Data.Vec.Base.du_replicate_444 (coe v6) (coe v1))
                (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Bounded.Base.split
d_split_206 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_split_206 = erased
-- Data.Vec.Bounded.Base.padBoth
d_padBoth_220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  AgdaAny ->
  AgdaAny -> T_Vec'8804'_126 -> MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_padBoth_220 ~v0 ~v1 v2 v3 v4 v5 = du_padBoth_220 v2 v3 v4 v5
du_padBoth_220 ::
  Integer ->
  AgdaAny ->
  AgdaAny -> T_Vec'8804'_126 -> MAlonzo.Code.Data.Vec.Base.T_Vec_28
du_padBoth_220 v0 v1 v2 v3
  = case coe v3 of
      C__'44'__144 v4 v5
        -> let v7 = coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v0 v4 in
           coe
             (coe
                MAlonzo.Code.Data.Vec.Base.du__'43''43'__188
                (coe
                   MAlonzo.Code.Data.Vec.Base.du_replicate_444
                   (coe MAlonzo.Code.Data.Nat.Base.d_'8970'_'47'2'8971'_264 (coe v7))
                   (coe v1))
                (coe
                   MAlonzo.Code.Data.Vec.Base.du__'43''43'__188 (coe v5)
                   (coe
                      MAlonzo.Code.Data.Vec.Base.du_replicate_444
                      (coe MAlonzo.Code.Data.Nat.Base.d_'8968'_'47'2'8969'_268 (coe v7))
                      (coe v2))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Bounded.Base.fromList
d_fromList_244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> T_Vec'8804'_126
d_fromList_244 ~v0 ~v1 v2 = du_fromList_244 v2
du_fromList_244 :: [AgdaAny] -> T_Vec'8804'_126
du_fromList_244 v0
  = coe
      du_fromVec_162 (coe MAlonzo.Code.Data.List.Base.du_length_284 v0)
      (coe MAlonzo.Code.Data.Vec.Base.du_fromList_600 (coe v0))
-- Data.Vec.Bounded.Base.toList
d_toList_246 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> T_Vec'8804'_126 -> [AgdaAny]
d_toList_246 ~v0 ~v1 ~v2 v3 = du_toList_246 v3
du_toList_246 :: T_Vec'8804'_126 -> [AgdaAny]
du_toList_246 v0
  = coe
      MAlonzo.Code.Data.Vec.Base.du_toList_592
      (coe du_toVec_156 (coe v0))
-- Data.Vec.Bounded.Base.replicate
d_replicate_250 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny -> T_Vec'8804'_126
d_replicate_250 v0 ~v1 ~v2 ~v3 ~v4 v5 = du_replicate_250 v0 v5
du_replicate_250 :: Integer -> AgdaAny -> T_Vec'8804'_126
du_replicate_250 v0 v1
  = coe
      C__'44'__144 v0
      (coe MAlonzo.Code.Data.Vec.Base.du_replicate_444 (coe v0) (coe v1))
-- Data.Vec.Bounded.Base.[]
d_'91''93'_256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> T_Vec'8804'_126
d_'91''93'_256 ~v0 ~v1 ~v2 = du_'91''93'_256
du_'91''93'_256 :: T_Vec'8804'_126
du_'91''93'_256
  = coe
      C__'44'__144 (0 :: Integer)
      (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)
-- Data.Vec.Bounded.Base._∷_
d__'8759'__258 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> AgdaAny -> T_Vec'8804'_126 -> T_Vec'8804'_126
d__'8759'__258 ~v0 ~v1 ~v2 v3 v4 = du__'8759'__258 v3 v4
du__'8759'__258 :: AgdaAny -> T_Vec'8804'_126 -> T_Vec'8804'_126
du__'8759'__258 v0 v1
  = case coe v1 of
      C__'44'__144 v2 v3
        -> coe
             C__'44'__144 (addInt (coe (1 :: Integer)) (coe v2))
             (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v0 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Bounded.Base.≤-cast
d_'8804''45'cast_268 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_Vec'8804'_126 -> T_Vec'8804'_126
d_'8804''45'cast_268 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8804''45'cast_268 v5
du_'8804''45'cast_268 :: T_Vec'8804'_126 -> T_Vec'8804'_126
du_'8804''45'cast_268 v0 = coe v0
-- Data.Vec.Bounded.Base.≡-cast
d_'8801''45'cast_278 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Vec'8804'_126 -> T_Vec'8804'_126
d_'8801''45'cast_278 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8801''45'cast_278 v5
du_'8801''45'cast_278 :: T_Vec'8804'_126 -> T_Vec'8804'_126
du_'8801''45'cast_278 v0 = coe v0
-- Data.Vec.Bounded.Base.map
d_map_282 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (AgdaAny -> AgdaAny) -> T_Vec'8804'_126 -> T_Vec'8804'_126
d_map_282 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 = du_map_282 v5 v6
du_map_282 ::
  (AgdaAny -> AgdaAny) -> T_Vec'8804'_126 -> T_Vec'8804'_126
du_map_282 v0 v1
  = case coe v1 of
      C__'44'__144 v2 v3
        -> coe
             C__'44'__144 v2
             (coe MAlonzo.Code.Data.Vec.Base.du_map_178 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Bounded.Base.reverse
d_reverse_290 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> T_Vec'8804'_126 -> T_Vec'8804'_126
d_reverse_290 ~v0 ~v1 ~v2 v3 = du_reverse_290 v3
du_reverse_290 :: T_Vec'8804'_126 -> T_Vec'8804'_126
du_reverse_290 v0
  = case coe v0 of
      C__'44'__144 v1 v2
        -> coe
             C__'44'__144 v1 (coe MAlonzo.Code.Data.Vec.Base.du_reverse_616 v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Bounded.Base.alignWith
d_alignWith_296 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (MAlonzo.Code.Data.These.Base.T_These_38 -> AgdaAny) ->
  T_Vec'8804'_126 -> T_Vec'8804'_126 -> T_Vec'8804'_126
d_alignWith_296 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9
  = du_alignWith_296 v7 v8 v9
du_alignWith_296 ::
  (MAlonzo.Code.Data.These.Base.T_These_38 -> AgdaAny) ->
  T_Vec'8804'_126 -> T_Vec'8804'_126 -> T_Vec'8804'_126
du_alignWith_296 v0 v1 v2
  = case coe v1 of
      C__'44'__144 v3 v4
        -> case coe v2 of
             C__'44'__144 v6 v7
               -> coe
                    C__'44'__144
                    (MAlonzo.Code.Data.Nat.Base.d__'8852'__204 (coe v3) (coe v6))
                    (coe
                       MAlonzo.Code.Data.Vec.Base.du_alignWith_204 (coe v0) (coe v4)
                       (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Bounded.Base.zipWith
d_zipWith_308 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_Vec'8804'_126 -> T_Vec'8804'_126 -> T_Vec'8804'_126
d_zipWith_308 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9
  = du_zipWith_308 v7 v8 v9
du_zipWith_308 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_Vec'8804'_126 -> T_Vec'8804'_126 -> T_Vec'8804'_126
du_zipWith_308 v0 v1 v2
  = case coe v1 of
      C__'44'__144 v3 v4
        -> case coe v2 of
             C__'44'__144 v6 v7
               -> coe
                    C__'44'__144
                    (MAlonzo.Code.Data.Nat.Base.d__'8851'__232 (coe v3) (coe v6))
                    (coe
                       MAlonzo.Code.Data.Vec.Base.du_restrictWith_224 (coe v0) (coe v4)
                       (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Bounded.Base.zip
d_zip_320 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_Vec'8804'_126 -> T_Vec'8804'_126 -> T_Vec'8804'_126
d_zip_320 ~v0 ~v1 ~v2 ~v3 ~v4 = du_zip_320
du_zip_320 :: T_Vec'8804'_126 -> T_Vec'8804'_126 -> T_Vec'8804'_126
du_zip_320
  = coe
      du_zipWith_308 (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32)
-- Data.Vec.Bounded.Base.align
d_align_322 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_Vec'8804'_126 -> T_Vec'8804'_126 -> T_Vec'8804'_126
d_align_322 ~v0 ~v1 ~v2 ~v3 ~v4 = du_align_322
du_align_322 ::
  T_Vec'8804'_126 -> T_Vec'8804'_126 -> T_Vec'8804'_126
du_align_322 = coe du_alignWith_296 (coe (\ v0 -> v0))
-- Data.Vec.Bounded.Base.take
d_take_326 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> Integer -> T_Vec'8804'_126 -> T_Vec'8804'_126
d_take_326 ~v0 ~v1 ~v2 v3 v4 = du_take_326 v3 v4
du_take_326 :: Integer -> T_Vec'8804'_126 -> T_Vec'8804'_126
du_take_326 v0 v1
  = case coe v0 of
      0 -> coe du_'91''93'_256
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                C__'44'__144 v3 v4
                  -> case coe v4 of
                       MAlonzo.Code.Data.Vec.Base.C_'91''93'_32 -> coe du_'91''93'_256
                       MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v7 v8
                         -> let v9 = subInt (coe v3) (coe (1 :: Integer)) in
                            coe
                              (coe
                                 du__'8759'__258 (coe v7)
                                 (coe du_take_326 (coe v2) (coe C__'44'__144 v9 v8)))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Vec.Bounded.Base.drop
d_drop_344 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> Integer -> T_Vec'8804'_126 -> T_Vec'8804'_126
d_drop_344 ~v0 ~v1 ~v2 v3 v4 = du_drop_344 v3 v4
du_drop_344 :: Integer -> T_Vec'8804'_126 -> T_Vec'8804'_126
du_drop_344 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                C__'44'__144 v3 v4
                  -> case coe v4 of
                       MAlonzo.Code.Data.Vec.Base.C_'91''93'_32 -> coe du_'91''93'_256
                       MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v7 v8
                         -> let v9 = subInt (coe v3) (coe (1 :: Integer)) in
                            coe (coe du_drop_344 (coe v2) (coe C__'44'__144 v9 v8))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Vec.Bounded.Base.rectangle
d_rectangle_362 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rectangle_362 ~v0 ~v1 v2 = du_rectangle_362 v2
du_rectangle_362 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_rectangle_362 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_width_374 (coe v0)) (coe du_padded_380 (coe v0))
-- Data.Vec.Bounded.Base._.sizes
d_sizes_372 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> [Integer]
d_sizes_372 ~v0 ~v1 v2 = du_sizes_372 v2
du_sizes_372 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> [Integer]
du_sizes_372 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_map_22
      (coe (\ v1 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1)))
      (coe v0)
-- Data.Vec.Bounded.Base._.width
d_width_374 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> Integer
d_width_374 ~v0 ~v1 v2 = du_width_374 v2
du_width_374 :: [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> Integer
du_width_374 v0
  = coe
      MAlonzo.Code.Data.List.Extrema.du_max_142
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2826
      (0 :: Integer) (coe du_sizes_372 (coe v0))
-- Data.Vec.Bounded.Base._.all≤
d_all'8804'_378 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_all'8804'_378 ~v0 ~v1 v2 = du_all'8804'_378 v2
du_all'8804'_378 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_all'8804'_378 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_map'8315'_684
      (coe v0)
      (coe
         MAlonzo.Code.Data.List.Extrema.du_xs'8804'max_720
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2826
         (0 :: Integer) (coe du_sizes_372 (coe v0)))
-- Data.Vec.Bounded.Base._.padded
d_padded_380 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> [T_Vec'8804'_126]
d_padded_380 ~v0 ~v1 v2 = du_padded_380 v2
du_padded_380 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> [T_Vec'8804'_126]
du_padded_380 v0
  = coe
      MAlonzo.Code.Data.List.Membership.Setoid.du_mapWith'8712'_62
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
      (coe v0)
      (coe
         (\ v1 v2 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v1)))
