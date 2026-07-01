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

module MAlonzo.Code.Data.Vec.Bounded.Base where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Extrema
import qualified MAlonzo.Code.Data.List.Membership.Setoid
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.All.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Data.These.Base
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Data.Vec.Bounded.Base._.argmax
d_argmax_10 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> Integer) -> AgdaAny -> [AgdaAny] -> AgdaAny
d_argmax_10 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Extrema.du_argmax_144
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v2
-- Data.Vec.Bounded.Base._.argmax-all
d_argmax'45'all_12 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
d_argmax'45'all_12 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Data.List.Extrema.du_argmax'45'all_518
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v3 v5 v6 v7 v8
-- Data.Vec.Bounded.Base._.argmax-sel
d_argmax'45'sel_14 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Integer) ->
  AgdaAny -> [AgdaAny] -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_argmax'45'sel_14 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Extrema.du_argmax'45'sel_506
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v2
-- Data.Vec.Bounded.Base._.argmax[xs]<argmax[ys]⁺
d_argmax'91'xs'93''60'argmax'91'ys'93''8314'_16 ::
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
d_argmax'91'xs'93''60'argmax'91'ys'93''8314'_16 v0 v1 v2 v3 v4 v5
                                                v6 v7 v8 v9
  = coe
      MAlonzo.Code.Data.List.Extrema.du_argmax'91'xs'93''60'argmax'91'ys'93''8314'_490
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v2 v3 v4 v5 v6 v7 v8 v9
-- Data.Vec.Bounded.Base._.argmax[xs]≤argmax[ys]⁺
d_argmax'91'xs'93''8804'argmax'91'ys'93''8314'_18 ::
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
d_argmax'91'xs'93''8804'argmax'91'ys'93''8314'_18 v0 v1 v2 v3 v4 v5
                                                  v6 v7 v8 v9
  = coe
      MAlonzo.Code.Data.List.Extrema.du_argmax'91'xs'93''8804'argmax'91'ys'93''8314'_462
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v2 v3 v4 v5 v6 v7 v8 v9
-- Data.Vec.Bounded.Base._.argmin
d_argmin_20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> Integer) -> AgdaAny -> [AgdaAny] -> AgdaAny
d_argmin_20 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Extrema.du_argmin_140
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v2
-- Data.Vec.Bounded.Base._.argmin-all
d_argmin'45'all_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> Integer) ->
  AgdaAny ->
  [AgdaAny] ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
d_argmin'45'all_22 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Data.List.Extrema.du_argmin'45'all_312
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v3 v4 v5 v7 v8
-- Data.Vec.Bounded.Base._.argmin-sel
d_argmin'45'sel_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Integer) ->
  AgdaAny -> [AgdaAny] -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_argmin'45'sel_24 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Extrema.du_argmin'45'sel_300
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v2
-- Data.Vec.Bounded.Base._.argmin[xs]<argmin[ys]⁺
d_argmin'91'xs'93''60'argmin'91'ys'93''8314'_26 ::
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
d_argmin'91'xs'93''60'argmin'91'ys'93''8314'_26 v0 v1 v2 v3 v4 v5
                                                v6 v7 v8 v9
  = coe
      MAlonzo.Code.Data.List.Extrema.du_argmin'91'xs'93''60'argmin'91'ys'93''8314'_284
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v2 v3 v4 v5 v6 v7 v8 v9
-- Data.Vec.Bounded.Base._.argmin[xs]≤argmin[ys]⁺
d_argmin'91'xs'93''8804'argmin'91'ys'93''8314'_28 ::
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
d_argmin'91'xs'93''8804'argmin'91'ys'93''8314'_28 v0 v1 v2 v3 v4 v5
                                                  v6 v7 v8 v9
  = coe
      MAlonzo.Code.Data.List.Extrema.du_argmin'91'xs'93''8804'argmin'91'ys'93''8314'_256
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v2 v3 v4 v5 v6 v7 v8 v9
-- Data.Vec.Bounded.Base._.f[argmax]<v⁺
d_f'91'argmax'93''60'v'8314'_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Integer) ->
  Integer ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_f'91'argmax'93''60'v'8314'_30 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.List.Extrema.du_f'91'argmax'93''60'v'8314'_404
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v2 v4 v5
-- Data.Vec.Bounded.Base._.f[argmax]≈f[v]⁺
d_f'91'argmax'93''8776'f'91'v'93''8314'_32 ::
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
d_f'91'argmax'93''8776'f'91'v'93''8314'_32 = erased
-- Data.Vec.Bounded.Base._.f[argmax]≤v⁺
d_f'91'argmax'93''8804'v'8314'_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Integer) ->
  Integer ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_f'91'argmax'93''8804'v'8314'_34 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.List.Extrema.du_f'91'argmax'93''8804'v'8314'_394
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v2 v4 v5
-- Data.Vec.Bounded.Base._.f[argmin]<v⁺
d_f'91'argmin'93''60'v'8314'_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Integer) ->
  Integer ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_f'91'argmin'93''60'v'8314'_36 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Extrema.du_f'91'argmin'93''60'v'8314'_178
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v2 v3
-- Data.Vec.Bounded.Base._.f[argmin]≈f[v]⁺
d_f'91'argmin'93''8776'f'91'v'93''8314'_38 ::
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
d_f'91'argmin'93''8776'f'91'v'93''8314'_38 = erased
-- Data.Vec.Bounded.Base._.f[argmin]≤f[xs]
d_f'91'argmin'93''8804'f'91'xs'93'_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Integer) ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_f'91'argmin'93''8804'f'91'xs'93'_40 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.List.Extrema.du_f'91'argmin'93''8804'f'91'xs'93'_216
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v2 v3 v4
-- Data.Vec.Bounded.Base._.f[argmin]≤f[⊤]
d_f'91'argmin'93''8804'f'91''8868''93'_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Integer) ->
  AgdaAny -> [AgdaAny] -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_f'91'argmin'93''8804'f'91''8868''93'_42 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.List.Extrema.du_f'91'argmin'93''8804'f'91''8868''93'_204
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v2 v3 v4
-- Data.Vec.Bounded.Base._.f[argmin]≤v⁺
d_f'91'argmin'93''8804'v'8314'_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Integer) ->
  Integer ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_f'91'argmin'93''8804'v'8314'_44 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Extrema.du_f'91'argmin'93''8804'v'8314'_168
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v2 v3
-- Data.Vec.Bounded.Base._.f[xs]≤f[argmax]
d_f'91'xs'93''8804'f'91'argmax'93'_46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Integer) ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_f'91'xs'93''8804'f'91'argmax'93'_46 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.List.Extrema.du_f'91'xs'93''8804'f'91'argmax'93'_422
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v2 v3 v4
-- Data.Vec.Bounded.Base._.f[⊥]≤f[argmax]
d_f'91''8869''93''8804'f'91'argmax'93'_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Integer) ->
  AgdaAny -> [AgdaAny] -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_f'91''8869''93''8804'f'91'argmax'93'_48 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.List.Extrema.du_f'91''8869''93''8804'f'91'argmax'93'_410
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v2 v3 v4
-- Data.Vec.Bounded.Base._.max
d_max_50 :: Integer -> [Integer] -> Integer
d_max_50
  = coe
      MAlonzo.Code.Data.List.Extrema.du_max_150
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
-- Data.Vec.Bounded.Base._.max-mono-⊆
d_max'45'mono'45''8838'_52 ::
  Integer ->
  Integer ->
  [Integer] ->
  [Integer] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'mono'45''8838'_52
  = coe
      MAlonzo.Code.Data.List.Extrema.du_max'45'mono'45''8838'_780
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
-- Data.Vec.Bounded.Base._.max<v⁺
d_max'60'v'8314'_54 ::
  Integer ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_max'60'v'8314'_54 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Extrema.du_max'60'v'8314'_694
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v1 v2
-- Data.Vec.Bounded.Base._.max[xs]<max[ys]⁺
d_max'91'xs'93''60'max'91'ys'93''8314'_56 ::
  Integer ->
  Integer ->
  [Integer] ->
  [Integer] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_max'91'xs'93''60'max'91'ys'93''8314'_56
  = coe
      MAlonzo.Code.Data.List.Extrema.du_max'91'xs'93''60'max'91'ys'93''8314'_770
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
-- Data.Vec.Bounded.Base._.max[xs]≤max[ys]⁺
d_max'91'xs'93''8804'max'91'ys'93''8314'_58 ::
  Integer ->
  Integer ->
  [Integer] ->
  [Integer] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'91'xs'93''8804'max'91'ys'93''8314'_58
  = coe
      MAlonzo.Code.Data.List.Extrema.du_max'91'xs'93''8804'max'91'ys'93''8314'_754
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
-- Data.Vec.Bounded.Base._.max≈v⁺
d_max'8776'v'8314'_60 ::
  Integer ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_max'8776'v'8314'_60 = erased
-- Data.Vec.Bounded.Base._.max≤v⁺
d_max'8804'v'8314'_62 ::
  Integer ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'8804'v'8314'_62 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Extrema.du_max'8804'v'8314'_684
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v1 v2
-- Data.Vec.Bounded.Base._.min
d_min_64 :: Integer -> [Integer] -> Integer
d_min_64
  = coe
      MAlonzo.Code.Data.List.Extrema.du_min_148
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
-- Data.Vec.Bounded.Base._.min-mono-⊆
d_min'45'mono'45''8838'_66 ::
  Integer ->
  Integer ->
  [Integer] ->
  [Integer] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_min'45'mono'45''8838'_66
  = coe
      MAlonzo.Code.Data.List.Extrema.du_min'45'mono'45''8838'_668
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
-- Data.Vec.Bounded.Base._.min<v⁺
d_min'60'v'8314'_68 ::
  Integer ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_min'60'v'8314'_68
  = coe
      MAlonzo.Code.Data.List.Extrema.du_min'60'v'8314'_582
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
-- Data.Vec.Bounded.Base._.min[xs]<min[ys]⁺
d_min'91'xs'93''60'min'91'ys'93''8314'_70 ::
  Integer ->
  Integer ->
  [Integer] ->
  [Integer] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_min'91'xs'93''60'min'91'ys'93''8314'_70
  = coe
      MAlonzo.Code.Data.List.Extrema.du_min'91'xs'93''60'min'91'ys'93''8314'_658
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
-- Data.Vec.Bounded.Base._.min[xs]≤min[ys]⁺
d_min'91'xs'93''8804'min'91'ys'93''8314'_72 ::
  Integer ->
  Integer ->
  [Integer] ->
  [Integer] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_min'91'xs'93''8804'min'91'ys'93''8314'_72
  = coe
      MAlonzo.Code.Data.List.Extrema.du_min'91'xs'93''8804'min'91'ys'93''8314'_642
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
-- Data.Vec.Bounded.Base._.min≈v⁺
d_min'8776'v'8314'_74 ::
  Integer ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_min'8776'v'8314'_74 = erased
-- Data.Vec.Bounded.Base._.min≤v⁺
d_min'8804'v'8314'_76 ::
  Integer ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_min'8804'v'8314'_76
  = coe
      MAlonzo.Code.Data.List.Extrema.du_min'8804'v'8314'_572
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
-- Data.Vec.Bounded.Base._.min≤xs
d_min'8804'xs_78 ::
  Integer ->
  [Integer] -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_min'8804'xs_78
  = coe
      MAlonzo.Code.Data.List.Extrema.du_min'8804'xs_616
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
-- Data.Vec.Bounded.Base._.min≤⊤
d_min'8804''8868'_80 ::
  Integer -> [Integer] -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_min'8804''8868'_80
  = coe
      MAlonzo.Code.Data.List.Extrema.du_min'8804''8868'_608
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
-- Data.Vec.Bounded.Base._.v<f[argmax]⁺
d_v'60'f'91'argmax'93''8314'_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Integer) ->
  Integer ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_v'60'f'91'argmax'93''8314'_82 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Extrema.du_v'60'f'91'argmax'93''8314'_384
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v2 v3
-- Data.Vec.Bounded.Base._.v<f[argmin]⁺
d_v'60'f'91'argmin'93''8314'_84 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Integer) ->
  Integer ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_v'60'f'91'argmin'93''8314'_84 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.List.Extrema.du_v'60'f'91'argmin'93''8314'_198
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v2 v4 v5
-- Data.Vec.Bounded.Base._.v<max⁺
d_v'60'max'8314'_86 ::
  Integer ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_v'60'max'8314'_86
  = coe
      MAlonzo.Code.Data.List.Extrema.du_v'60'max'8314'_714
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
-- Data.Vec.Bounded.Base._.v<min⁺
d_v'60'min'8314'_88 ::
  Integer ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_v'60'min'8314'_88 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Extrema.du_v'60'min'8314'_602
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v1 v2
-- Data.Vec.Bounded.Base._.v≤f[argmax]⁺
d_v'8804'f'91'argmax'93''8314'_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Integer) ->
  Integer ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_v'8804'f'91'argmax'93''8314'_90 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Extrema.du_v'8804'f'91'argmax'93''8314'_374
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v2 v3
-- Data.Vec.Bounded.Base._.v≤f[argmin]⁺
d_v'8804'f'91'argmin'93''8314'_92 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Integer) ->
  Integer ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_v'8804'f'91'argmin'93''8314'_92 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.List.Extrema.du_v'8804'f'91'argmin'93''8314'_188
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v2 v4 v5
-- Data.Vec.Bounded.Base._.v≤max⁺
d_v'8804'max'8314'_94 ::
  Integer ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_v'8804'max'8314'_94
  = coe
      MAlonzo.Code.Data.List.Extrema.du_v'8804'max'8314'_704
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
-- Data.Vec.Bounded.Base._.v≤min⁺
d_v'8804'min'8314'_96 ::
  Integer ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_v'8804'min'8314'_96 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Extrema.du_v'8804'min'8314'_592
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
      v1 v2
-- Data.Vec.Bounded.Base._.xs≤max
d_xs'8804'max_98 ::
  Integer ->
  [Integer] -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_xs'8804'max_98
  = coe
      MAlonzo.Code.Data.List.Extrema.du_xs'8804'max_728
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
-- Data.Vec.Bounded.Base._.⊥≤max
d_'8869''8804'max_100 ::
  Integer -> [Integer] -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8869''8804'max_100
  = coe
      MAlonzo.Code.Data.List.Extrema.du_'8869''8804'max_720
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966)
-- Data.Vec.Bounded.Base.Vec≤
d_Vec'8804'_126 a0 a1 a2 = ()
data T_Vec'8804'_126
  = C__'44'__144 Integer MAlonzo.Code.Data.Vec.Base.T_Vec_28
-- Data.Vec.Bounded.Base.Vec≤.length
d_length_138 :: T_Vec'8804'_126 -> Integer
d_length_138 v0
  = case coe v0 of
      C__'44'__144 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Bounded.Base.Vec≤.vec
d_vec_140 :: T_Vec'8804'_126 -> MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_vec_140 v0
  = case coe v0 of
      C__'44'__144 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
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
             (MAlonzo.Code.Data.Nat.Properties.d__'8804''63'__2920
                (coe v2) (coe v0))
             erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Bounded.Base.toVec
d_toVec_156 ::
  T_Vec'8804'_126 -> MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_toVec_156 v0
  = case coe v0 of
      C__'44'__144 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
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
                   (coe MAlonzo.Code.Data.Nat.Base.d_'8970'_'47'2'8971'_268 (coe v7))
                   (coe v1))
                (coe
                   MAlonzo.Code.Data.Vec.Base.du__'43''43'__188 (coe v5)
                   (coe
                      MAlonzo.Code.Data.Vec.Base.du_replicate_444
                      (coe MAlonzo.Code.Data.Nat.Base.d_'8968'_'47'2'8969'_272 (coe v7))
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
      du_fromVec_162 (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
      (coe MAlonzo.Code.Data.Vec.Base.du_fromList_600 (coe v0))
-- Data.Vec.Bounded.Base.toList
d_toList_246 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> T_Vec'8804'_126 -> [AgdaAny]
d_toList_246 ~v0 ~v1 ~v2 v3 = du_toList_246 v3
du_toList_246 :: T_Vec'8804'_126 -> [AgdaAny]
du_toList_246 v0
  = coe
      MAlonzo.Code.Data.Vec.Base.du_toList_592 (coe d_vec_140 (coe v0))
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
                    (MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v3) (coe v6))
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
                    (MAlonzo.Code.Data.Nat.Base.d__'8851'__236 (coe v3) (coe v6))
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
      MAlonzo.Code.Data.List.Extrema.du_max_150
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966
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
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_map'8315'_504
      (coe v0)
      (coe
         MAlonzo.Code.Data.List.Extrema.du_xs'8804'max_728
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2966
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
      MAlonzo.Code.Data.List.Membership.Setoid.du_mapWith'8712'_64
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
      (coe v0)
      (coe
         (\ v1 v2 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v1)))
