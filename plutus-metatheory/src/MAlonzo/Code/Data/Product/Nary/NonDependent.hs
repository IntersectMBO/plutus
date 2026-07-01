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

module MAlonzo.Code.Data.Product.Nary.NonDependent where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Data.Product.Properties
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Level
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Data.Product.Nary.NonDependent.Product⊤
d_Product'8868'_12 :: Integer -> AgdaAny -> AgdaAny -> ()
d_Product'8868'_12 = erased
-- Data.Product.Nary.NonDependent.Product
d_Product_26 :: Integer -> AgdaAny -> AgdaAny -> ()
d_Product_26 = erased
-- Data.Product.Nary.NonDependent.HomoProduct′
d_HomoProduct'8242'_40 ::
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> ()) -> ()
d_HomoProduct'8242'_40 = erased
-- Data.Product.Nary.NonDependent.HomoProduct
d_HomoProduct_50 ::
  Integer -> MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()
d_HomoProduct_50 = erased
-- Data.Product.Nary.NonDependent.Pointwiseₙ
d_Pointwise'8345'_70 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   () -> AgdaAny -> AgdaAny -> ()) ->
  Integer -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_Pointwise'8345'_70 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      0 -> coe
             MAlonzo.Code.Level.C_lift_20
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      1 -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                v0 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)) v4 v5)
             (coe
                MAlonzo.Code.Level.C_lift_20
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              v0 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                              (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)) v6 v8)
                           (coe
                              d_Pointwise'8345'_70 erased
                              (coe subInt (coe v1) (coe (1 :: Integer)))
                              (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
                              (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3)) (coe v7)
                              (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Product.Nary.NonDependent.Equalₙ
d_Equal'8345'_106 ::
  Integer -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_Equal'8345'_106 = coe d_Pointwise'8345'_70 erased
-- Data.Product.Nary.NonDependent.toProduct
d_toProduct_114 ::
  Integer -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_toProduct_114 v0 ~v1 ~v2 v3 = du_toProduct_114 v0 v3
du_toProduct_114 :: Integer -> AgdaAny -> AgdaAny
du_toProduct_114 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      1 -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3 -> coe v2
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                    (coe
                       du_toProduct_114 (coe subInt (coe v0) (coe (1 :: Integer)))
                       (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Product.Nary.NonDependent.toProduct⊤
d_toProduct'8868'_130 ::
  Integer -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_toProduct'8868'_130 v0 ~v1 ~v2 v3 = du_toProduct'8868'_130 v0 v3
du_toProduct'8868'_130 :: Integer -> AgdaAny -> AgdaAny
du_toProduct'8868'_130 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      1 -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                    (coe
                       du_toProduct'8868'_130 (coe subInt (coe v0) (coe (1 :: Integer)))
                       (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Product.Nary.NonDependent.curryₙ
d_curry'8345'_150 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny
d_curry'8345'_150 v0 ~v1 ~v2 ~v3 ~v4 v5 = du_curry'8345'_150 v0 v5
du_curry'8345'_150 :: Integer -> (AgdaAny -> AgdaAny) -> AgdaAny
du_curry'8345'_150 v0 v1
  = case coe v0 of
      0 -> coe v1 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      1 -> coe v1
      _ -> coe
             MAlonzo.Code.Function.Base.du__'8728''8242'__216
             (coe du_curry'8345'_150 (coe subInt (coe v0) (coe (1 :: Integer))))
             (coe MAlonzo.Code.Data.Product.Base.du_curry_224 (coe v1))
-- Data.Product.Nary.NonDependent.uncurryₙ
d_uncurry'8345'_170 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> AgdaAny -> AgdaAny
d_uncurry'8345'_170 v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_uncurry'8345'_170 v0 v5
du_uncurry'8345'_170 :: Integer -> AgdaAny -> AgdaAny -> AgdaAny
du_uncurry'8345'_170 v0 v1
  = case coe v0 of
      0 -> coe (\ v2 -> v1)
      1 -> coe v1
      _ -> coe
             MAlonzo.Code.Data.Product.Base.du_uncurry_244
             (coe
                MAlonzo.Code.Function.Base.du__'8728''8242'__216
                (coe
                   du_uncurry'8345'_170 (coe subInt (coe v0) (coe (1 :: Integer))))
                (coe v1))
-- Data.Product.Nary.NonDependent.curry⊤ₙ
d_curry'8868''8345'_190 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny
d_curry'8868''8345'_190 v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_curry'8868''8345'_190 v0 v5
du_curry'8868''8345'_190 ::
  Integer -> (AgdaAny -> AgdaAny) -> AgdaAny
du_curry'8868''8345'_190 v0 v1
  = case coe v0 of
      0 -> coe v1 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Function.Base.du__'8728''8242'__216
                (coe du_curry'8868''8345'_190 (coe v2))
                (coe MAlonzo.Code.Data.Product.Base.du_curry_224 (coe v1)))
-- Data.Product.Nary.NonDependent.uncurry⊤ₙ
d_uncurry'8868''8345'_208 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> AgdaAny -> AgdaAny
d_uncurry'8868''8345'_208 v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_uncurry'8868''8345'_208 v0 v5
du_uncurry'8868''8345'_208 ::
  Integer -> AgdaAny -> AgdaAny -> AgdaAny
du_uncurry'8868''8345'_208 v0 v1
  = case coe v0 of
      0 -> coe (\ v2 -> v1)
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Product.Base.du_uncurry_244
                (coe
                   MAlonzo.Code.Function.Base.du__'8728''8242'__216
                   (coe du_uncurry'8868''8345'_208 (coe v2)) (coe v1)))
-- Data.Product.Nary.NonDependent.Product⊤-dec
d_Product'8868''45'dec_222 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_Product'8868''45'dec_222 v0 ~v1 ~v2 v3
  = du_Product'8868''45'dec_222 v0 v3
du_Product'8868''45'dec_222 ::
  Integer ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_Product'8868''45'dec_222 v0 v1
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                       (coe v3) (coe du_Product'8868''45'dec_222 (coe v2) (coe v4))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Product.Nary.NonDependent.Product-dec
d_Product'45'dec_236 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_Product'45'dec_236 v0 ~v1 ~v2 v3 = du_Product'45'dec_236 v0 v3
du_Product'45'dec_236 ::
  Integer ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_Product'45'dec_236 v0 v1
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      1 -> coe v1
      _ -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                    (coe v2)
                    (coe
                       du_Product'45'dec_236 (coe subInt (coe v0) (coe (1 :: Integer)))
                       (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Product.Nary.NonDependent.toEqualₙ
d_toEqual'8345'_256 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_toEqual'8345'_256 v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_toEqual'8345'_256 v0 v5
du_toEqual'8345'_256 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_toEqual'8345'_256 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      1 -> coe v1
      _ -> coe
             MAlonzo.Code.Data.Product.Base.du_map'8322'_150
             (\ v2 ->
                coe
                  du_toEqual'8345'_256 (coe subInt (coe v0) (coe (1 :: Integer))))
             (coe MAlonzo.Code.Data.Product.Properties.du_'44''45'injective_142)
-- Data.Product.Nary.NonDependent.fromEqualₙ
d_fromEqual'8345'_276 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromEqual'8345'_276 = erased
-- Data.Product.Nary.NonDependent.Levelₙ
d_Level'8345'_288 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18
d_Level'8345'_288 ~v0 v1 v2 = du_Level'8345'_288 v1 v2
du_Level'8345'_288 ::
  AgdaAny ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18
du_Level'8345'_288 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> case coe v0 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4 -> coe v3
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v3
        -> case coe v0 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe du_Level'8345'_288 (coe v5) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Product.Nary.NonDependent.Projₙ
d_Proj'8345'_302 ::
  Integer ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> ()
d_Proj'8345'_302 = erased
-- Data.Product.Nary.NonDependent.projₙ
d_proj'8345'_318 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny -> AgdaAny
d_proj'8345'_318 v0 ~v1 ~v2 v3 v4 = du_proj'8345'_318 v0 v3 v4
du_proj'8345'_318 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny -> AgdaAny
du_proj'8345'_318 v0 v1 v2
  = case coe v0 of
      1 -> coe seq (coe v1) (coe v2)
      _ -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5 -> coe v4
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v4
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> coe
                           du_proj'8345'_318 (coe subInt (coe v0) (coe (1 :: Integer)))
                           (coe v4) (coe v6)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Product.Nary.NonDependent.zipWith
d_zipWith_348 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
d_zipWith_348 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9
  = du_zipWith_348 v0 v7 v8 v9
du_zipWith_348 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
du_zipWith_348 v0 v1 v2 v3
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      1 -> coe v1 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12) v2 v3
      _ -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe v1 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12) v4 v6)
                           (coe
                              du_zipWith_348 (coe subInt (coe v0) (coe (1 :: Integer)))
                              (coe (\ v8 -> coe v1 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v8)))
                              (coe v5) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Product.Nary.NonDependent.Levelₙ⁻
d_Level'8345''8315'_374 ::
  Integer ->
  AgdaAny -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d_Level'8345''8315'_374 ~v0 v1 v2 = du_Level'8345''8315'_374 v1 v2
du_Level'8345''8315'_374 ::
  AgdaAny -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
du_Level'8345''8315'_374 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> case coe v0 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4 -> coe v4
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v3
        -> case coe v0 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                    (coe du_Level'8345''8315'_374 (coe v5) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Product.Nary.NonDependent.Removeₙ
d_Remove'8345'_390 ::
  Integer ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d_Remove'8345'_390 ~v0 ~v1 v2 v3 = du_Remove'8345'_390 v2 v3
du_Remove'8345'_390 ::
  AgdaAny -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
du_Remove'8345'_390 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> case coe v0 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4 -> coe v4
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v3
        -> case coe v0 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                    (coe du_Remove'8345'_390 (coe v5) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Product.Nary.NonDependent.removeₙ
d_remove'8345'_408 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny -> AgdaAny
d_remove'8345'_408 v0 ~v1 ~v2 v3 v4 = du_remove'8345'_408 v0 v3 v4
du_remove'8345'_408 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny -> AgdaAny
du_remove'8345'_408 v0 v1 v2
  = case coe v0 of
      1 -> coe seq (coe v1) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5 -> coe v5
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v4
               -> case coe v0 of
                    2 -> case coe v2 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6 -> coe v5
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> case coe v2 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                                  (coe
                                     du_remove'8345'_408 (coe subInt (coe v0) (coe (1 :: Integer)))
                                     (coe v4) (coe v6))
                           _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Product.Nary.NonDependent.Levelₙ⁺
d_Level'8345''8314'_424 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_Level'8345''8314'_424 ~v0 v1 v2 v3
  = du_Level'8345''8314'_424 v1 v2 v3
du_Level'8345''8314'_424 ::
  AgdaAny ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_Level'8345''8314'_424 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v0)
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v4
        -> case coe v0 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                    (coe du_Level'8345''8314'_424 (coe v6) (coe v4) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Product.Nary.NonDependent.Insertₙ
d_Insert'8345'_448 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  AgdaAny ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  () -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_Insert'8345'_448 ~v0 ~v1 ~v2 v3 v4 v5
  = du_Insert'8345'_448 v3 v4 v5
du_Insert'8345'_448 ::
  AgdaAny ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  () -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_Insert'8345'_448 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v0)
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v4
        -> case coe v0 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                    (coe du_Insert'8345'_448 (coe v6) (coe v4) erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Product.Nary.NonDependent.insertₙ
d_insert'8345'_476 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  AgdaAny ->
  () ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_insert'8345'_476 v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_insert'8345'_476 v0 v5 v6 v7
du_insert'8345'_476 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_insert'8345'_476 v0 v1 v2 v3
  = case coe v0 of
      0 -> coe seq (coe v1) (coe v2)
      _ -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v5
               -> case coe v0 of
                    1 -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                           (coe
                              du_insert'8345'_476 (coe (0 :: Integer)) (coe v5) (coe v2)
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    _ -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                  (coe
                                     du_insert'8345'_476 (coe subInt (coe v0) (coe (1 :: Integer)))
                                     (coe v5) (coe v2) (coe v7))
                           _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Product.Nary.NonDependent.Levelₙᵘ
d_Level'8345''7512'_506 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> AgdaAny
d_Level'8345''7512'_506 ~v0 v1 v2 v3
  = du_Level'8345''7512'_506 v1 v2 v3
du_Level'8345''7512'_506 ::
  AgdaAny ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> AgdaAny
du_Level'8345''7512'_506 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> case coe v0 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v4
        -> case coe v0 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                    (coe du_Level'8345''7512'_506 (coe v6) (coe v4) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Product.Nary.NonDependent.Updateₙ
d_Update'8345'_532 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  AgdaAny -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> () -> AgdaAny
d_Update'8345'_532 ~v0 ~v1 ~v2 v3 v4 v5
  = du_Update'8345'_532 v3 v4 v5
du_Update'8345'_532 ::
  AgdaAny -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> () -> AgdaAny
du_Update'8345'_532 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> case coe v0 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v4
        -> case coe v0 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                    (coe du_Update'8345'_532 (coe v6) (coe v4) erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Product.Nary.NonDependent.updateₙ
d_update'8345'_564 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  AgdaAny ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (AgdaAny -> ()) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_update'8345'_564 v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7
  = du_update'8345'_564 v0 v4 v6 v7
du_update'8345'_564 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_update'8345'_564 v0 v1 v2 v3
  = case coe v0 of
      1 -> coe seq (coe v1) (coe v2 v3)
      _ -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2 v5) (coe v6)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v5
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                           (coe
                              du_update'8345'_564 (coe subInt (coe v0) (coe (1 :: Integer)))
                              (coe v5) (coe v2) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Product.Nary.NonDependent.updateₙ′
d_update'8345''8242'_600 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  AgdaAny ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_update'8345''8242'_600 v0 ~v1 ~v2 ~v3 v4 ~v5
  = du_update'8345''8242'_600 v0 v4
du_update'8345''8242'_600 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_update'8345''8242'_600 v0 v1
  = coe du_update'8345'_564 (coe v0) (coe v1)
-- Data.Product.Nary.NonDependent.Allₙ
d_All'8345'_606 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   () -> AgdaAny -> AgdaAny -> ()) ->
  Integer -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_All'8345'_606 = coe d_Pointwise'8345'_70
