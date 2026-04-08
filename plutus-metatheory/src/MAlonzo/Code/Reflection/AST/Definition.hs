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

module MAlonzo.Code.Reflection.AST.Definition where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Reflection
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.List.Properties
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Reflection.AST.Argument
import qualified MAlonzo.Code.Reflection.AST.Argument.QQuantity
import qualified MAlonzo.Code.Reflection.AST.Name
import qualified MAlonzo.Code.Reflection.AST.Term
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Reflection.AST.Definition.function-injective
d_function'45'injective_10 ::
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160] ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_function'45'injective_10 = erased
-- Reflection.AST.Definition.data-type-injective₁
d_data'45'type'45'injective'8321'_20 ::
  Integer ->
  Integer ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_data'45'type'45'injective'8321'_20 = erased
-- Reflection.AST.Definition.data-type-injective₂
d_data'45'type'45'injective'8322'_30 ::
  Integer ->
  Integer ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_data'45'type'45'injective'8322'_30 = erased
-- Reflection.AST.Definition.data-type-injective
d_data'45'type'45'injective_40 ::
  Integer ->
  Integer ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_data'45'type'45'injective_40 ~v0 ~v1 ~v2 ~v3
  = du_data'45'type'45'injective_40
du_data'45'type'45'injective_40 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_data'45'type'45'injective_40
  = coe
      MAlonzo.Code.Data.Product.Base.du_'60'_'44'_'62'_112 erased erased
-- Reflection.AST.Definition.record′-injective₁
d_record'8242''45'injective'8321'_50 ::
  AgdaAny ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_record'8242''45'injective'8321'_50 = erased
-- Reflection.AST.Definition.record′-injective₂
d_record'8242''45'injective'8322'_60 ::
  AgdaAny ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_record'8242''45'injective'8322'_60 = erased
-- Reflection.AST.Definition.record′-injective
d_record'8242''45'injective_70 ::
  AgdaAny ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_record'8242''45'injective_70 ~v0 ~v1 ~v2 ~v3
  = du_record'8242''45'injective_70
du_record'8242''45'injective_70 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_record'8242''45'injective_70
  = coe
      MAlonzo.Code.Data.Product.Base.du_'60'_'44'_'62'_112 erased erased
-- Reflection.AST.Definition.constructor′-injective₁
d_constructor'8242''45'injective'8321'_80 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Quantity_62 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Quantity_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_constructor'8242''45'injective'8321'_80 = erased
-- Reflection.AST.Definition.constructor′-injective₂
d_constructor'8242''45'injective'8322'_90 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Quantity_62 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Quantity_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_constructor'8242''45'injective'8322'_90 = erased
-- Reflection.AST.Definition.constructor′-injective
d_constructor'8242''45'injective_100 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Quantity_62 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Quantity_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_constructor'8242''45'injective_100 ~v0 ~v1 ~v2 ~v3
  = du_constructor'8242''45'injective_100
du_constructor'8242''45'injective_100 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_constructor'8242''45'injective_100
  = coe
      MAlonzo.Code.Data.Product.Base.du_'60'_'44'_'62'_112 erased erased
-- Reflection.AST.Definition._≟_
d__'8799'__102 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Definition_280 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Definition_280 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__102 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_function_284 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Reflection.C_function_284 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                    erased erased
                    (coe
                       MAlonzo.Code.Reflection.AST.Term.d__'8799''45'Clauses__222 (coe v2)
                       (coe v3))
             MAlonzo.Code.Agda.Builtin.Reflection.C_data'45'type_290 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Agda.Builtin.Reflection.C_record'45'type_296 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Agda.Builtin.Reflection.C_data'45'cons_302 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Agda.Builtin.Reflection.C_axiom_304
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Agda.Builtin.Reflection.C_prim'45'fun_306
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Reflection.C_data'45'type_290 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Reflection.C_function_284 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Agda.Builtin.Reflection.C_data'45'type_290 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                    (coe MAlonzo.Code.Data.Product.Base.du_uncurry_244 erased)
                    (coe du_data'45'type'45'injective_40)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v2) (coe v4))
                       (coe
                          MAlonzo.Code.Data.List.Properties.du_'8801''45'dec_60
                          (coe MAlonzo.Code.Reflection.AST.Name.d__'8799'__12) (coe v3)
                          (coe v5)))
             MAlonzo.Code.Agda.Builtin.Reflection.C_record'45'type_296 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Agda.Builtin.Reflection.C_data'45'cons_302 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Agda.Builtin.Reflection.C_axiom_304
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Agda.Builtin.Reflection.C_prim'45'fun_306
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Reflection.C_record'45'type_296 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Reflection.C_function_284 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Agda.Builtin.Reflection.C_data'45'type_290 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Agda.Builtin.Reflection.C_record'45'type_296 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                    (coe MAlonzo.Code.Data.Product.Base.du_uncurry_244 erased)
                    (coe du_record'8242''45'injective_70)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                       (coe
                          MAlonzo.Code.Reflection.AST.Name.d__'8799'__12 (coe v2) (coe v4))
                       (coe
                          MAlonzo.Code.Data.List.Properties.du_'8801''45'dec_60
                          (coe
                             MAlonzo.Code.Reflection.AST.Argument.du_'8801''45'dec_96
                             (coe MAlonzo.Code.Reflection.AST.Name.d__'8799'__12))
                          (coe v3) (coe v5)))
             MAlonzo.Code.Agda.Builtin.Reflection.C_data'45'cons_302 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Agda.Builtin.Reflection.C_axiom_304
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Agda.Builtin.Reflection.C_prim'45'fun_306
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Reflection.C_data'45'cons_302 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Reflection.C_function_284 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Agda.Builtin.Reflection.C_data'45'type_290 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Agda.Builtin.Reflection.C_record'45'type_296 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Agda.Builtin.Reflection.C_data'45'cons_302 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                    (coe MAlonzo.Code.Data.Product.Base.du_uncurry_244 erased)
                    (coe du_constructor'8242''45'injective_100)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                       (coe
                          MAlonzo.Code.Reflection.AST.Name.d__'8799'__12 (coe v2) (coe v4))
                       (coe
                          MAlonzo.Code.Reflection.AST.Argument.QQuantity.d__'8799'__8
                          (coe v3) (coe v5)))
             MAlonzo.Code.Agda.Builtin.Reflection.C_axiom_304
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Agda.Builtin.Reflection.C_prim'45'fun_306
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Reflection.C_axiom_304
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Reflection.C_function_284 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Agda.Builtin.Reflection.C_data'45'type_290 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Agda.Builtin.Reflection.C_record'45'type_296 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Agda.Builtin.Reflection.C_data'45'cons_302 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Agda.Builtin.Reflection.C_axiom_304
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Agda.Builtin.Reflection.C_prim'45'fun_306
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Reflection.C_prim'45'fun_306
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Reflection.C_function_284 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Agda.Builtin.Reflection.C_data'45'type_290 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Agda.Builtin.Reflection.C_record'45'type_296 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Agda.Builtin.Reflection.C_data'45'cons_302 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Agda.Builtin.Reflection.C_axiom_304
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Agda.Builtin.Reflection.C_prim'45'fun_306
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
