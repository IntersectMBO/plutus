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

module MAlonzo.Code.Data.String where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Char.Properties
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Extrema
import qualified MAlonzo.Code.Data.List.Membership.DecSetoid
import qualified MAlonzo.Code.Data.List.Membership.Propositional
import qualified MAlonzo.Code.Data.List.Membership.Setoid
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Data.String._.argmax
d_argmax_6 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> Integer) -> AgdaAny -> [AgdaAny] -> AgdaAny
d_argmax_6 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Extrema.du_argmax_144
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v2
-- Data.String._.argmax-all
d_argmax'45'all_8 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
d_argmax'45'all_8 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Data.List.Extrema.du_argmax'45'all_518
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v3 v5 v6 v7 v8
-- Data.String._.argmax-sel
d_argmax'45'sel_10 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Integer) ->
  AgdaAny -> [AgdaAny] -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_argmax'45'sel_10 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Extrema.du_argmax'45'sel_506
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v2
-- Data.String._.argmax[xs]<argmax[ys]⁺
d_argmax'91'xs'93''60'argmax'91'ys'93''8314'_12 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_argmax'91'xs'93''60'argmax'91'ys'93''8314'_12 v0 v1 v2 v3 v4 v5
                                                v6 v7 v8 v9
  = coe
      MAlonzo.Code.Data.List.Extrema.du_argmax'91'xs'93''60'argmax'91'ys'93''8314'_490
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v2 v3 v4 v5 v6 v7 v8 v9
-- Data.String._.argmax[xs]≤argmax[ys]⁺
d_argmax'91'xs'93''8804'argmax'91'ys'93''8314'_14 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_argmax'91'xs'93''8804'argmax'91'ys'93''8314'_14 v0 v1 v2 v3 v4 v5
                                                  v6 v7 v8 v9
  = coe
      MAlonzo.Code.Data.List.Extrema.du_argmax'91'xs'93''8804'argmax'91'ys'93''8314'_462
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v2 v3 v4 v5 v6 v7 v8 v9
-- Data.String._.argmin
d_argmin_16 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> Integer) -> AgdaAny -> [AgdaAny] -> AgdaAny
d_argmin_16 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Extrema.du_argmin_140
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v2
-- Data.String._.argmin-all
d_argmin'45'all_18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> Integer) ->
  AgdaAny ->
  [AgdaAny] ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
d_argmin'45'all_18 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Data.List.Extrema.du_argmin'45'all_312
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v3 v4 v5 v7 v8
-- Data.String._.argmin-sel
d_argmin'45'sel_20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Integer) ->
  AgdaAny -> [AgdaAny] -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_argmin'45'sel_20 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Extrema.du_argmin'45'sel_300
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v2
-- Data.String._.argmin[xs]<argmin[ys]⁺
d_argmin'91'xs'93''60'argmin'91'ys'93''8314'_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_argmin'91'xs'93''60'argmin'91'ys'93''8314'_22 v0 v1 v2 v3 v4 v5
                                                v6 v7 v8 v9
  = coe
      MAlonzo.Code.Data.List.Extrema.du_argmin'91'xs'93''60'argmin'91'ys'93''8314'_284
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v2 v3 v4 v5 v6 v7 v8 v9
-- Data.String._.argmin[xs]≤argmin[ys]⁺
d_argmin'91'xs'93''8804'argmin'91'ys'93''8314'_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_argmin'91'xs'93''8804'argmin'91'ys'93''8314'_24 v0 v1 v2 v3 v4 v5
                                                  v6 v7 v8 v9
  = coe
      MAlonzo.Code.Data.List.Extrema.du_argmin'91'xs'93''8804'argmin'91'ys'93''8314'_256
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v2 v3 v4 v5 v6 v7 v8 v9
-- Data.String._.f[argmax]<v⁺
d_f'91'argmax'93''60'v'8314'_26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Integer) ->
  Integer ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_f'91'argmax'93''60'v'8314'_26 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.List.Extrema.du_f'91'argmax'93''60'v'8314'_404
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v2 v4 v5
-- Data.String._.f[argmax]≈f[v]⁺
d_f'91'argmax'93''8776'f'91'v'93''8314'_28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Integer) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_f'91'argmax'93''8776'f'91'v'93''8314'_28 = erased
-- Data.String._.f[argmax]≤v⁺
d_f'91'argmax'93''8804'v'8314'_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Integer) ->
  Integer ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_f'91'argmax'93''8804'v'8314'_30 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.List.Extrema.du_f'91'argmax'93''8804'v'8314'_394
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v2 v4 v5
-- Data.String._.f[argmin]<v⁺
d_f'91'argmin'93''60'v'8314'_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Integer) ->
  Integer ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_f'91'argmin'93''60'v'8314'_32 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Extrema.du_f'91'argmin'93''60'v'8314'_178
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v2 v3
-- Data.String._.f[argmin]≈f[v]⁺
d_f'91'argmin'93''8776'f'91'v'93''8314'_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Integer) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_f'91'argmin'93''8776'f'91'v'93''8314'_34 = erased
-- Data.String._.f[argmin]≤f[xs]
d_f'91'argmin'93''8804'f'91'xs'93'_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Integer) ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_f'91'argmin'93''8804'f'91'xs'93'_36 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.List.Extrema.du_f'91'argmin'93''8804'f'91'xs'93'_216
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v2 v3 v4
-- Data.String._.f[argmin]≤f[⊤]
d_f'91'argmin'93''8804'f'91''8868''93'_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Integer) ->
  AgdaAny -> [AgdaAny] -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_f'91'argmin'93''8804'f'91''8868''93'_38 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.List.Extrema.du_f'91'argmin'93''8804'f'91''8868''93'_204
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v2 v3 v4
-- Data.String._.f[argmin]≤v⁺
d_f'91'argmin'93''8804'v'8314'_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Integer) ->
  Integer ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_f'91'argmin'93''8804'v'8314'_40 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Extrema.du_f'91'argmin'93''8804'v'8314'_168
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v2 v3
-- Data.String._.f[xs]≤f[argmax]
d_f'91'xs'93''8804'f'91'argmax'93'_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Integer) ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_f'91'xs'93''8804'f'91'argmax'93'_42 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.List.Extrema.du_f'91'xs'93''8804'f'91'argmax'93'_422
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v2 v3 v4
-- Data.String._.f[⊥]≤f[argmax]
d_f'91''8869''93''8804'f'91'argmax'93'_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Integer) ->
  AgdaAny -> [AgdaAny] -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_f'91''8869''93''8804'f'91'argmax'93'_44 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.List.Extrema.du_f'91''8869''93''8804'f'91'argmax'93'_410
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v2 v3 v4
-- Data.String._.max
d_max_46 :: Integer -> [Integer] -> Integer
d_max_46
  = coe
      MAlonzo.Code.Data.List.Extrema.du_max_150
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
-- Data.String._.max-mono-⊆
d_max'45'mono'45''8838'_48 ::
  Integer ->
  Integer ->
  [Integer] ->
  [Integer] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'mono'45''8838'_48
  = coe
      MAlonzo.Code.Data.List.Extrema.du_max'45'mono'45''8838'_780
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
-- Data.String._.max<v⁺
d_max'60'v'8314'_50 ::
  Integer ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_max'60'v'8314'_50 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Extrema.du_max'60'v'8314'_694
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v1 v2
-- Data.String._.max[xs]<max[ys]⁺
d_max'91'xs'93''60'max'91'ys'93''8314'_52 ::
  Integer ->
  Integer ->
  [Integer] ->
  [Integer] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_max'91'xs'93''60'max'91'ys'93''8314'_52
  = coe
      MAlonzo.Code.Data.List.Extrema.du_max'91'xs'93''60'max'91'ys'93''8314'_770
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
-- Data.String._.max[xs]≤max[ys]⁺
d_max'91'xs'93''8804'max'91'ys'93''8314'_54 ::
  Integer ->
  Integer ->
  [Integer] ->
  [Integer] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'91'xs'93''8804'max'91'ys'93''8314'_54
  = coe
      MAlonzo.Code.Data.List.Extrema.du_max'91'xs'93''8804'max'91'ys'93''8314'_754
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
-- Data.String._.max≈v⁺
d_max'8776'v'8314'_56 ::
  Integer ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_max'8776'v'8314'_56 = erased
-- Data.String._.max≤v⁺
d_max'8804'v'8314'_58 ::
  Integer ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'8804'v'8314'_58 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Extrema.du_max'8804'v'8314'_684
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v1 v2
-- Data.String._.min
d_min_60 :: Integer -> [Integer] -> Integer
d_min_60
  = coe
      MAlonzo.Code.Data.List.Extrema.du_min_148
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
-- Data.String._.min-mono-⊆
d_min'45'mono'45''8838'_62 ::
  Integer ->
  Integer ->
  [Integer] ->
  [Integer] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_min'45'mono'45''8838'_62
  = coe
      MAlonzo.Code.Data.List.Extrema.du_min'45'mono'45''8838'_668
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
-- Data.String._.min<v⁺
d_min'60'v'8314'_64 ::
  Integer ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_min'60'v'8314'_64
  = coe
      MAlonzo.Code.Data.List.Extrema.du_min'60'v'8314'_582
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
-- Data.String._.min[xs]<min[ys]⁺
d_min'91'xs'93''60'min'91'ys'93''8314'_66 ::
  Integer ->
  Integer ->
  [Integer] ->
  [Integer] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_min'91'xs'93''60'min'91'ys'93''8314'_66
  = coe
      MAlonzo.Code.Data.List.Extrema.du_min'91'xs'93''60'min'91'ys'93''8314'_658
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
-- Data.String._.min[xs]≤min[ys]⁺
d_min'91'xs'93''8804'min'91'ys'93''8314'_68 ::
  Integer ->
  Integer ->
  [Integer] ->
  [Integer] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_min'91'xs'93''8804'min'91'ys'93''8314'_68
  = coe
      MAlonzo.Code.Data.List.Extrema.du_min'91'xs'93''8804'min'91'ys'93''8314'_642
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
-- Data.String._.min≈v⁺
d_min'8776'v'8314'_70 ::
  Integer ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_min'8776'v'8314'_70 = erased
-- Data.String._.min≤v⁺
d_min'8804'v'8314'_72 ::
  Integer ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_min'8804'v'8314'_72
  = coe
      MAlonzo.Code.Data.List.Extrema.du_min'8804'v'8314'_572
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
-- Data.String._.min≤xs
d_min'8804'xs_74 ::
  Integer ->
  [Integer] -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_min'8804'xs_74
  = coe
      MAlonzo.Code.Data.List.Extrema.du_min'8804'xs_616
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
-- Data.String._.min≤⊤
d_min'8804''8868'_76 ::
  Integer -> [Integer] -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_min'8804''8868'_76
  = coe
      MAlonzo.Code.Data.List.Extrema.du_min'8804''8868'_608
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
-- Data.String._.v<f[argmax]⁺
d_v'60'f'91'argmax'93''8314'_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Integer) ->
  Integer ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_v'60'f'91'argmax'93''8314'_78 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Extrema.du_v'60'f'91'argmax'93''8314'_384
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v2 v3
-- Data.String._.v<f[argmin]⁺
d_v'60'f'91'argmin'93''8314'_80 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Integer) ->
  Integer ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_v'60'f'91'argmin'93''8314'_80 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.List.Extrema.du_v'60'f'91'argmin'93''8314'_198
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v2 v4 v5
-- Data.String._.v<max⁺
d_v'60'max'8314'_82 ::
  Integer ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_v'60'max'8314'_82
  = coe
      MAlonzo.Code.Data.List.Extrema.du_v'60'max'8314'_714
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
-- Data.String._.v<min⁺
d_v'60'min'8314'_84 ::
  Integer ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_v'60'min'8314'_84 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Extrema.du_v'60'min'8314'_602
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v1 v2
-- Data.String._.v≤f[argmax]⁺
d_v'8804'f'91'argmax'93''8314'_86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Integer) ->
  Integer ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_v'8804'f'91'argmax'93''8314'_86 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Extrema.du_v'8804'f'91'argmax'93''8314'_374
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v2 v3
-- Data.String._.v≤f[argmin]⁺
d_v'8804'f'91'argmin'93''8314'_88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Integer) ->
  Integer ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_v'8804'f'91'argmin'93''8314'_88 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.List.Extrema.du_v'8804'f'91'argmin'93''8314'_188
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v2 v4 v5
-- Data.String._.v≤max⁺
d_v'8804'max'8314'_90 ::
  Integer ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_v'8804'max'8314'_90
  = coe
      MAlonzo.Code.Data.List.Extrema.du_v'8804'max'8314'_704
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
-- Data.String._.v≤min⁺
d_v'8804'min'8314'_92 ::
  Integer ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_v'8804'min'8314'_92 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Extrema.du_v'8804'min'8314'_592
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v1 v2
-- Data.String._.xs≤max
d_xs'8804'max_94 ::
  Integer ->
  [Integer] -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_xs'8804'max_94
  = coe
      MAlonzo.Code.Data.List.Extrema.du_xs'8804'max_728
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
-- Data.String._.⊥≤max
d_'8869''8804'max_96 ::
  Integer -> [Integer] -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8869''8804'max_96
  = coe
      MAlonzo.Code.Data.List.Extrema.du_'8869''8804'max_720
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
-- Data.String._._∈_
d__'8712'__100 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> ()
d__'8712'__100 = erased
-- Data.String._._∈?_
d__'8712''63'__102 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8712''63'__102
  = let v0 = MAlonzo.Code.Data.Char.Properties.d__'8799'__14 in
    coe
      (coe
         MAlonzo.Code.Data.List.Membership.DecSetoid.du__'8712''63'__60
         (coe
            MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
            (coe v0)))
-- Data.String._._∉_
d__'8713'__104 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> ()
d__'8713'__104 = erased
-- Data.String._._∉?_
d__'8713''63'__106 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8713''63'__106
  = let v0 = MAlonzo.Code.Data.Char.Properties.d__'8799'__14 in
    coe
      (coe
         MAlonzo.Code.Data.List.Membership.DecSetoid.du__'8713''63'__68
         (coe
            MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
            (coe v0)))
-- Data.String._._∷=_
d__'8759''61'__108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  (MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> ()) ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d__'8759''61'__108
  = coe MAlonzo.Code.Data.List.Membership.Setoid.du__'8759''61'__52
-- Data.String._._≢∈_
d__'8802''8712'__110 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 -> ()
d__'8802''8712'__110 = erased
-- Data.String._._─_
d__'9472'__112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> ()) ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d__'9472'__112
  = coe MAlonzo.Code.Data.List.Membership.Setoid.du__'9472'__54
-- Data.String._.find
d_find_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> ()) ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_find_114 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Membership.Setoid.du_find_86
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
      v2 v3
-- Data.String._.lose
d_lose_116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> ()) ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_lose_116 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Membership.Propositional.du_lose_50 v2 v3
-- Data.String._.mapWith∈
d_mapWith'8712'_118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  (MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 -> AgdaAny) ->
  [AgdaAny]
d_mapWith'8712'_118 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Membership.Setoid.du_mapWith'8712'_64
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
      v2 v3
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
            MAlonzo.Code.Data.List.Membership.DecSetoid.du__'8712''63'__60
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
      MAlonzo.Code.Data.List.Extrema.du_max_150
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966
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
