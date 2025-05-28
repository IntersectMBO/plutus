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

module MAlonzo.Code.Reflection.AST.Abstraction where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.Reflection qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Builtin.String qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.Product.Base qualified
import MAlonzo.Code.Data.String.Properties qualified
import MAlonzo.Code.Relation.Nullary.Decidable.Core qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Reflection.AST.Abstraction.map
d_map_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Abs_112 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Abs_112
d_map_22 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_map_22 v4 v5
du_map_22 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Abs_112 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Abs_112
du_map_22 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 (coe v2) (coe v0 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.AST.Abstraction.abs-injective₁
d_abs'45'injective'8321'_30 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abs'45'injective'8321'_30 = erased
-- Reflection.AST.Abstraction.abs-injective₂
d_abs'45'injective'8322'_32 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abs'45'injective'8322'_32 = erased
-- Reflection.AST.Abstraction.abs-injective
d_abs'45'injective_34 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_abs'45'injective_34 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_abs'45'injective_34
du_abs'45'injective_34 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_abs'45'injective_34
  = coe
      MAlonzo.Code.Data.Product.Base.du_'60'_'44'_'62'_112 erased erased
-- Reflection.AST.Abstraction.unAbs
d_unAbs_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Agda.Builtin.Reflection.T_Abs_112 -> AgdaAny
d_unAbs_36 ~v0 ~v1 v2 = du_unAbs_36 v2
du_unAbs_36 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Abs_112 -> AgdaAny
du_unAbs_36 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 v1 v2 -> coe v2
      _                                                    -> MAlonzo.RTE.mazUnreachableError
-- Reflection.AST.Abstraction.unAbs-dec
d_unAbs'45'dec_46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Abs_112 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Abs_112 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_unAbs'45'dec_46 ~v0 ~v1 v2 v3 v4 = du_unAbs'45'dec_46 v2 v3 v4
du_unAbs'45'dec_46 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Abs_112 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Abs_112 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_unAbs'45'dec_46 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
                    (coe MAlonzo.Code.Data.Product.Base.du_uncurry_244 erased)
                    (coe du_abs'45'injective_34)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__76
                       (coe
                          MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v3)
                          (coe v5))
                       (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.AST.Abstraction.≡-dec
d_'8801''45'dec_58 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Abs_112 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Abs_112 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8801''45'dec_58 ~v0 ~v1 v2 v3 v4 = du_'8801''45'dec_58 v2 v3 v4
du_'8801''45'dec_58 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Abs_112 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Abs_112 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8801''45'dec_58 v0 v1 v2
  = coe
      du_unAbs'45'dec_46 (coe v1) (coe v2)
      (coe v0 (coe du_unAbs_36 (coe v1)) (coe du_unAbs_36 (coe v2)))
