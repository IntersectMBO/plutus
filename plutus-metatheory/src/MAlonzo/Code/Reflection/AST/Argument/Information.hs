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

module MAlonzo.Code.Reflection.AST.Argument.Information where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Reflection
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Reflection.AST.Argument.Modality
import qualified MAlonzo.Code.Reflection.AST.Argument.Visibility
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Reflection.AST.Argument.Information.visibility
d_visibility_16 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_ArgInfo_76 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Visibility_48
d_visibility_16 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82 v1 v2
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.AST.Argument.Information.modality
d_modality_20 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_ArgInfo_76 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Modality_68
d_modality_20 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82 v1 v2
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.AST.Argument.Information.arg-info-injective₁
d_arg'45'info'45'injective'8321'_24 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Visibility_48 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Modality_68 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Visibility_48 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Modality_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arg'45'info'45'injective'8321'_24 = erased
-- Reflection.AST.Argument.Information.arg-info-injective₂
d_arg'45'info'45'injective'8322'_26 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Visibility_48 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Modality_68 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Visibility_48 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Modality_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arg'45'info'45'injective'8322'_26 = erased
-- Reflection.AST.Argument.Information.arg-info-injective
d_arg'45'info'45'injective_28 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Visibility_48 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Modality_68 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Visibility_48 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Modality_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_arg'45'info'45'injective_28 ~v0 ~v1 ~v2 ~v3
  = du_arg'45'info'45'injective_28
du_arg'45'info'45'injective_28 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_arg'45'info'45'injective_28
  = coe
      MAlonzo.Code.Data.Product.Base.du_'60'_'44'_'62'_112 erased erased
-- Reflection.AST.Argument.Information._≟_
d__'8799'__30 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_ArgInfo_76 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_ArgInfo_76 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__30 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                    (coe MAlonzo.Code.Data.Product.Base.du_uncurry_244 erased)
                    (coe du_arg'45'info'45'injective_28)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                       (coe
                          MAlonzo.Code.Reflection.AST.Argument.Visibility.d__'8799'__8
                          (coe v2) (coe v4))
                       (coe
                          MAlonzo.Code.Reflection.AST.Argument.Modality.d__'8799'__30
                          (coe v3) (coe v5)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
