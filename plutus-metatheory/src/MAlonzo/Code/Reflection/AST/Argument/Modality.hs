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

module MAlonzo.Code.Reflection.AST.Argument.Modality where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Reflection
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Reflection.AST.Argument.QQuantity
import qualified MAlonzo.Code.Reflection.AST.Argument.Relevance
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Reflection.AST.Argument.Modality.relevance
d_relevance_16 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Modality_68 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Relevance_56
d_relevance_16 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.AST.Argument.Modality.quantity
d_quantity_20 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Modality_68 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Quantity_62
d_quantity_20 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.AST.Argument.Modality.modality-injective₁
d_modality'45'injective'8321'_24 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Relevance_56 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Quantity_62 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Relevance_56 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Quantity_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modality'45'injective'8321'_24 = erased
-- Reflection.AST.Argument.Modality.modality-injective₂
d_modality'45'injective'8322'_26 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Relevance_56 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Quantity_62 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Relevance_56 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Quantity_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modality'45'injective'8322'_26 = erased
-- Reflection.AST.Argument.Modality.modality-injective
d_modality'45'injective_28 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Relevance_56 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Quantity_62 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Relevance_56 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Quantity_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_modality'45'injective_28 ~v0 ~v1 ~v2 ~v3
  = du_modality'45'injective_28
du_modality'45'injective_28 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_modality'45'injective_28
  = coe
      MAlonzo.Code.Data.Product.Base.du_'60'_'44'_'62'_112 erased erased
-- Reflection.AST.Argument.Modality._≟_
d__'8799'__30 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Modality_68 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Modality_68 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__30 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                    (coe MAlonzo.Code.Data.Product.Base.du_uncurry_244 erased)
                    (coe du_modality'45'injective_28)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                       (coe
                          MAlonzo.Code.Reflection.AST.Argument.Relevance.d__'8799'__8
                          (coe v2) (coe v4))
                       (coe
                          MAlonzo.Code.Reflection.AST.Argument.QQuantity.d__'8799'__8
                          (coe v3) (coe v5)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
