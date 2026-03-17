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

module MAlonzo.Code.Data.Vec.NZ45Zary where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Function.Bundles

-- Data.Vec.N-ary.N-ary-level
d_N'45'ary'45'level_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  Integer -> MAlonzo.Code.Agda.Primitive.T_Level_18
d_N'45'ary'45'level_24 v0 v1 v2
  = case coe v2 of
      0 -> coe v1
      _ -> let v3 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Agda.Primitive.d__'8852'__30 v0
                (d_N'45'ary'45'level_24 (coe v0) (coe v1) (coe v3)))
-- Data.Vec.N-ary.N-ary
d_N'45'ary_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> Integer -> () -> () -> ()
d_N'45'ary_38 = erased
-- Data.Vec.N-ary.curryⁿ
d_curry'8319'_52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny) -> AgdaAny
d_curry'8319'_52 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_curry'8319'_52 v4 v5
du_curry'8319'_52 ::
  Integer ->
  (MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny) -> AgdaAny
du_curry'8319'_52 v0 v1
  = case coe v0 of
      0 -> coe v1 (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                (\ v3 ->
                   coe
                     du_curry'8319'_52 (coe v2)
                     (coe
                        (\ v4 ->
                           coe v1 (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v3 v4)))))
-- Data.Vec.N-ary._$ⁿ_
d__'36''8319'__64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny
d__'36''8319'__64 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du__'36''8319'__64 v5 v6
du__'36''8319'__64 ::
  AgdaAny -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny
du__'36''8319'__64 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Vec.Base.C_'91''93'_32 -> coe v0
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v3 v4
        -> coe du__'36''8319'__64 (coe v0 v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.N-ary._.∀ⁿ
d_'8704''8319'_84 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> Integer -> AgdaAny -> ()
d_'8704''8319'_84 = erased
-- Data.Vec.N-ary._.∀ⁿʰ
d_'8704''8319''688'_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> Integer -> AgdaAny -> ()
d_'8704''8319''688'_96 = erased
-- Data.Vec.N-ary._.∃ⁿ
d_'8707''8319'_108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> Integer -> AgdaAny -> ()
d_'8707''8319'_108 = erased
-- Data.Vec.N-ary.Eq
d_Eq_126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  () ->
  Integer -> (AgdaAny -> AgdaAny -> ()) -> AgdaAny -> AgdaAny -> ()
d_Eq_126 = erased
-- Data.Vec.N-ary.Eqʰ
d_Eq'688'_146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  () ->
  Integer -> (AgdaAny -> AgdaAny -> ()) -> AgdaAny -> AgdaAny -> ()
d_Eq'688'_146 = erased
-- Data.Vec.N-ary.left-inverse
d_left'45'inverse_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny) ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_left'45'inverse_164 = erased
-- Data.Vec.N-ary.right-inverse
d_right'45'inverse_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> AgdaAny -> AgdaAny
d_right'45'inverse_178 ~v0 ~v1 ~v2 ~v3 v4 ~v5
  = du_right'45'inverse_178 v4
du_right'45'inverse_178 :: Integer -> AgdaAny
du_right'45'inverse_178 v0
  = case coe v0 of
      0 -> erased
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe (coe (\ v2 -> coe du_right'45'inverse_178 (coe v1)))
-- Data.Vec.N-ary.uncurry-∀ⁿ
d_uncurry'45''8704''8319'_194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Function.Bundles.T_Equivalence_1810
d_uncurry'45''8704''8319'_194 ~v0 ~v1 ~v2 v3 ~v4
  = du_uncurry'45''8704''8319'_194 v3
du_uncurry'45''8704''8319'_194 ::
  Integer -> MAlonzo.Code.Function.Bundles.T_Equivalence_1810
du_uncurry'45''8704''8319'_194 v0
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8660'_2414
      (coe du_'8658'_214 (coe v0)) (coe du_'8656'_232 (coe v0))
-- Data.Vec.N-ary._.⇒
d_'8658'_214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  Integer ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny
d_'8658'_214 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 v8
  = du_'8658'_214 v5 v7 v8
du_'8658'_214 ::
  Integer ->
  AgdaAny -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny
du_'8658'_214 v0 v1 v2
  = case coe v0 of
      0 -> coe seq (coe v2) (coe v1)
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v2 of
                MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v5 v6
                  -> coe du_'8658'_214 (coe v3) (coe v1 v5) (coe v6)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Vec.N-ary._.⇐
d_'8656'_232 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  Integer ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  (MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny) -> AgdaAny
d_'8656'_232 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 = du_'8656'_232 v5 v7
du_'8656'_232 ::
  Integer ->
  (MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny) -> AgdaAny
du_'8656'_232 v0 v1
  = case coe v0 of
      0 -> coe v1 (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                (\ v3 ->
                   coe
                     du_'8656'_232 (coe v2)
                     (coe
                        (\ v4 ->
                           coe v1 (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v3 v4)))))
-- Data.Vec.N-ary.uncurry-∃ⁿ
d_uncurry'45''8707''8319'_248 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Function.Bundles.T_Equivalence_1810
d_uncurry'45''8707''8319'_248 ~v0 ~v1 ~v2 v3 ~v4
  = du_uncurry'45''8707''8319'_248 v3
du_uncurry'45''8707''8319'_248 ::
  Integer -> MAlonzo.Code.Function.Bundles.T_Equivalence_1810
du_uncurry'45''8707''8319'_248 v0
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8660'_2414
      (coe du_'8658'_268 (coe v0)) (coe du_'8656'_284 (coe v0))
-- Data.Vec.N-ary._.⇒
d_'8658'_268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  Integer ->
  AgdaAny ->
  Integer ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8658'_268 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 = du_'8658'_268 v5 v7
du_'8658'_268 ::
  Integer -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8658'_268 v0 v1
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32) (coe v1)
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                  -> coe
                       MAlonzo.Code.Data.Product.Base.du_map_128
                       (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 (coe v3))
                       (coe (\ v5 v6 -> v6)) (coe du_'8658'_268 (coe v2) (coe v4))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Vec.N-ary._.⇐
d_'8656'_284 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  Integer ->
  AgdaAny ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_'8656'_284 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 = du_'8656'_284 v5 v7
du_'8656'_284 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_'8656'_284 v0 v1
  = case coe v0 of
      0 -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
               -> coe seq (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                  -> case coe v3 of
                       MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v6 v7
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                              (coe
                                 du_'8656'_284 (coe v2)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7) (coe v4)))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Vec.N-ary._.curryⁿ-cong
d_curry'8319''45'cong_316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny) ->
  (MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny) ->
  (MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny) -> AgdaAny
d_curry'8319''45'cong_316 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
                          ~v10 v11
  = du_curry'8319''45'cong_316 v8 v11
du_curry'8319''45'cong_316 ::
  Integer ->
  (MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny) -> AgdaAny
du_curry'8319''45'cong_316 v0 v1
  = case coe v0 of
      0 -> coe v1 (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                (\ v3 ->
                   coe
                     du_curry'8319''45'cong_316 (coe v2)
                     (coe
                        (\ v4 ->
                           coe v1 (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v3 v4)))))
-- Data.Vec.N-ary._.curryⁿ-cong⁻¹
d_curry'8319''45'cong'8315''185'_344 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny) ->
  (MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny
d_curry'8319''45'cong'8315''185'_344 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                     ~v7 ~v8 ~v9 ~v10 v11 v12
  = du_curry'8319''45'cong'8315''185'_344 v11 v12
du_curry'8319''45'cong'8315''185'_344 ::
  AgdaAny -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny
du_curry'8319''45'cong'8315''185'_344 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Vec.Base.C_'91''93'_32 -> coe v0
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v3 v4
        -> coe du_curry'8319''45'cong'8315''185'_344 (coe v0 v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.N-ary._.appⁿ-cong
d_app'8319''45'cong_370 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny
d_app'8319''45'cong_370 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 v11 v12
  = du_app'8319''45'cong_370 v11 v12
du_app'8319''45'cong_370 ::
  AgdaAny -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny
du_app'8319''45'cong_370 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Vec.Base.C_'91''93'_32 -> coe v0
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v3 v4
        -> coe du_app'8319''45'cong_370 (coe v0 v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.N-ary._.appⁿ-cong⁻¹
d_app'8319''45'cong'8315''185'_396 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny) -> AgdaAny
d_app'8319''45'cong'8315''185'_396 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                   v8 ~v9 ~v10 v11
  = du_app'8319''45'cong'8315''185'_396 v8 v11
du_app'8319''45'cong'8315''185'_396 ::
  Integer ->
  (MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny) -> AgdaAny
du_app'8319''45'cong'8315''185'_396 v0 v1
  = case coe v0 of
      0 -> coe v1 (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                (\ v3 ->
                   coe
                     du_app'8319''45'cong'8315''185'_396 (coe v2)
                     (coe
                        (\ v4 ->
                           coe v1 (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v3 v4)))))
-- Data.Vec.N-ary.Eq-to-Eqʰ
d_Eq'45'to'45'Eq'688'_424 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_Eq'45'to'45'Eq'688'_424 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9
                          ~v10 v11
  = du_Eq'45'to'45'Eq'688'_424 v7 v11
du_Eq'45'to'45'Eq'688'_424 :: Integer -> AgdaAny -> AgdaAny
du_Eq'45'to'45'Eq'688'_424 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe (\ v3 -> coe du_Eq'45'to'45'Eq'688'_424 (coe v2) (coe v1 v3)))
-- Data.Vec.N-ary.Eqʰ-to-Eq
d_Eq'688''45'to'45'Eq_444 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_Eq'688''45'to'45'Eq_444 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9
                          ~v10 v11
  = du_Eq'688''45'to'45'Eq_444 v7 v11
du_Eq'688''45'to'45'Eq_444 :: Integer -> AgdaAny -> AgdaAny
du_Eq'688''45'to'45'Eq_444 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe (\ v3 -> coe du_Eq'688''45'to'45'Eq_444 (coe v2) (coe v1 v3)))
-- Data.Vec.N-ary._.Vec↔N-ary
d_Vec'8596'N'45'ary_470 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   () ->
   (AgdaAny -> ()) ->
   (AgdaAny -> AgdaAny) ->
   (AgdaAny -> AgdaAny) ->
   (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> MAlonzo.Code.Function.Bundles.T_Inverse_2068
d_Vec'8596'N'45'ary_470 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_Vec'8596'N'45'ary_470 v5
du_Vec'8596'N'45'ary_470 ::
  Integer -> MAlonzo.Code.Function.Bundles.T_Inverse_2068
du_Vec'8596'N'45'ary_470 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2482
             (coe
                (\ v1 -> coe v1 (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)))
             (coe (\ v1 v2 -> v1))
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2482
                (coe
                   (\ v2 v3 ->
                      coe
                        MAlonzo.Code.Function.Bundles.d_to_2080
                        (coe du_Vec'8596'N'45'ary_470 (coe v1))
                        (\ v4 ->
                           coe v2 (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v3 v4))))
                (coe
                   (\ v2 v3 ->
                      coe
                        MAlonzo.Code.Function.Bundles.d_from_2082
                        (coe du_Vec'8596'N'45'ary_470 (coe v1))
                        (coe v2 (coe MAlonzo.Code.Data.Vec.Base.du_head_70 (coe v3)))
                        (coe MAlonzo.Code.Data.Vec.Base.du_tail_76 (coe v3)))))
-- Data.Vec.N-ary._..extendedlambda0
d_'46'extendedlambda0_478 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   () ->
   (AgdaAny -> ()) ->
   (AgdaAny -> AgdaAny) ->
   (AgdaAny -> AgdaAny) ->
   (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny) ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'46'extendedlambda0_478 = erased
-- Data.Vec.N-ary._..extendedlambda0
d_'46'extendedlambda0_580 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   () ->
   (AgdaAny -> ()) ->
   (AgdaAny -> AgdaAny) ->
   (AgdaAny -> AgdaAny) ->
   (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny) ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'46'extendedlambda0_580 = erased
