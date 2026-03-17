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

module MAlonzo.Code.Data.Nat.ListAction.Properties where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Divisibility
import qualified MAlonzo.Code.Data.Nat.Divisibility.Core
import qualified MAlonzo.Code.Data.Nat.ListAction
import qualified MAlonzo.Code.Data.Nat.Properties

-- Data.Nat.ListAction.Properties.sum-++
d_sum'45''43''43'_20 ::
  [Integer] ->
  [Integer] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sum'45''43''43'_20 = erased
-- Data.Nat.ListAction.Properties.sum-↭
d_sum'45''8621'_36 ::
  [Integer] ->
  [Integer] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sum'45''8621'_36 = erased
-- Data.Nat.ListAction.Properties.product-++
d_product'45''43''43'_120 ::
  [Integer] ->
  [Integer] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_product'45''43''43'_120 = erased
-- Data.Nat.ListAction.Properties.∈⇒∣product
d_'8712''8658''8739'product_136 ::
  Integer ->
  [Integer] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_'8712''8658''8739'product_136 ~v0 v1 v2
  = du_'8712''8658''8739'product_136 v1 v2
du_'8712''8658''8739'product_136 ::
  [Integer] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_'8712''8658''8739'product_136 v0 v1
  = case coe v0 of
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v6
               -> coe
                    MAlonzo.Code.Data.Nat.Divisibility.du_m'8739'm'42'n_346
                    (coe MAlonzo.Code.Data.Nat.ListAction.d_product_8 v3)
             MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v6
               -> coe
                    MAlonzo.Code.Data.Nat.Divisibility.du_'8739'n'8658''8739'm'42'n_374
                    v2 (coe du_'8712''8658''8739'product_136 (coe v3) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.ListAction.Properties.product≢0
d_product'8802'0_148 ::
  [Integer] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_product'8802'0_148 ~v0 v1 = du_product'8802'0_148 v1
du_product'8802'0_148 ::
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_product'8802'0_148 v0
  = case coe v0 of
      MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_NonZero'46'constructor_3575
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v3 v4
        -> coe MAlonzo.Code.Data.Nat.Properties.du_m'42'n'8802'0_3872
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.ListAction.Properties.∈⇒≤product
d_'8712''8658''8804'product_154 ::
  [Integer] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8712''8658''8804'product_154 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v6 v7
        -> case coe v0 of
             (:) v8 v9
               -> case coe v3 of
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v12
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'42'n_4182 (coe v1)
                           (coe
                              MAlonzo.Code.Data.List.Base.du_foldr_216 (coe mulInt)
                              (coe (1 :: Integer)) (coe v9))
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v12
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'8658'm'8804'o'42'n_4204
                           (coe
                              MAlonzo.Code.Data.List.Base.du_foldr_216 (coe mulInt)
                              (coe (1 :: Integer)) (coe v9))
                           (coe v8)
                           (coe
                              d_'8712''8658''8804'product_154 (coe v9) (coe v1) (coe v7)
                              (coe v12))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.ListAction.Properties.product-↭
d_product'45''8621'_166 ::
  [Integer] ->
  [Integer] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_product'45''8621'_166 = erased
