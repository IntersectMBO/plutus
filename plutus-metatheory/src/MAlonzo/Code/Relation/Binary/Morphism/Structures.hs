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

module MAlonzo.Code.Relation.Binary.Morphism.Structures where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive

-- Relation.Binary.Morphism.Structures._.Homomorphic₂
d_Homomorphic'8322'_18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8322'_18 = erased
-- Relation.Binary.Morphism.Structures.IsRelHomomorphism
d_IsRelHomomorphism_42 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
newtype T_IsRelHomomorphism_42
  = C_constructor_54 (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Relation.Binary.Morphism.Structures.IsRelHomomorphism.cong
d_cong_52 ::
  T_IsRelHomomorphism_42 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_52 v0
  = case coe v0 of
      C_constructor_54 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Morphism.Structures.IsRelMonomorphism
d_IsRelMonomorphism_66 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_IsRelMonomorphism_66
  = C_constructor_86 T_IsRelHomomorphism_42
                     (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Relation.Binary.Morphism.Structures.IsRelMonomorphism.isHomomorphism
d_isHomomorphism_78 ::
  T_IsRelMonomorphism_66 -> T_IsRelHomomorphism_42
d_isHomomorphism_78 v0
  = case coe v0 of
      C_constructor_86 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Morphism.Structures.IsRelMonomorphism.injective
d_injective_80 ::
  T_IsRelMonomorphism_66 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_80 v0
  = case coe v0 of
      C_constructor_86 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Morphism.Structures.IsRelMonomorphism._.cong
d_cong_84 ::
  T_IsRelMonomorphism_66 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_84 v0 = coe d_cong_52 (coe d_isHomomorphism_78 (coe v0))
-- Relation.Binary.Morphism.Structures.IsRelIsomorphism
d_IsRelIsomorphism_98 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_IsRelIsomorphism_98
  = C_constructor_124 T_IsRelMonomorphism_66
                      (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Relation.Binary.Morphism.Structures.IsRelIsomorphism.isMonomorphism
d_isMonomorphism_110 ::
  T_IsRelIsomorphism_98 -> T_IsRelMonomorphism_66
d_isMonomorphism_110 v0
  = case coe v0 of
      C_constructor_124 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Morphism.Structures.IsRelIsomorphism.surjective
d_surjective_112 ::
  T_IsRelIsomorphism_98 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_112 v0
  = case coe v0 of
      C_constructor_124 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Morphism.Structures.IsRelIsomorphism._.cong
d_cong_116 ::
  T_IsRelIsomorphism_98 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_116 v0
  = coe
      d_cong_52
      (coe d_isHomomorphism_78 (coe d_isMonomorphism_110 (coe v0)))
-- Relation.Binary.Morphism.Structures.IsRelIsomorphism._.injective
d_injective_118 ::
  T_IsRelIsomorphism_98 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_118 v0
  = coe d_injective_80 (coe d_isMonomorphism_110 (coe v0))
-- Relation.Binary.Morphism.Structures.IsRelIsomorphism._.isHomomorphism
d_isHomomorphism_120 ::
  T_IsRelIsomorphism_98 -> T_IsRelHomomorphism_42
d_isHomomorphism_120 v0
  = coe d_isHomomorphism_78 (coe d_isMonomorphism_110 (coe v0))
-- Relation.Binary.Morphism.Structures.IsRelIsomorphism.bijective
d_bijective_122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsRelIsomorphism_98 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bijective_122 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_bijective_122 v9
du_bijective_122 ::
  T_IsRelIsomorphism_98 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bijective_122 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe d_injective_80 (coe d_isMonomorphism_110 (coe v0)))
      (coe d_surjective_112 (coe v0))
-- Relation.Binary.Morphism.Structures.IsOrderHomomorphism
d_IsOrderHomomorphism_144 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
  = ()
data T_IsOrderHomomorphism_144
  = C_constructor_170 (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Relation.Binary.Morphism.Structures.IsOrderHomomorphism.cong
d_cong_160 ::
  T_IsOrderHomomorphism_144 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_160 v0
  = case coe v0 of
      C_constructor_170 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Morphism.Structures.IsOrderHomomorphism.mono
d_mono_162 ::
  T_IsOrderHomomorphism_144 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_mono_162 v0
  = case coe v0 of
      C_constructor_170 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Morphism.Structures.IsOrderHomomorphism.Eq.isRelHomomorphism
d_isRelHomomorphism_166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsOrderHomomorphism_144 -> T_IsRelHomomorphism_42
d_isRelHomomorphism_166 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 ~v11 ~v12 v13
  = du_isRelHomomorphism_166 v13
du_isRelHomomorphism_166 ::
  T_IsOrderHomomorphism_144 -> T_IsRelHomomorphism_42
du_isRelHomomorphism_166 v0
  = coe C_constructor_54 (coe d_cong_160 (coe v0))
-- Relation.Binary.Morphism.Structures.IsOrderHomomorphism.isRelHomomorphism
d_isRelHomomorphism_168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsOrderHomomorphism_144 -> T_IsRelHomomorphism_42
d_isRelHomomorphism_168 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 ~v11 ~v12 v13
  = du_isRelHomomorphism_168 v13
du_isRelHomomorphism_168 ::
  T_IsOrderHomomorphism_144 -> T_IsRelHomomorphism_42
du_isRelHomomorphism_168 v0
  = coe C_constructor_54 (coe d_mono_162 (coe v0))
-- Relation.Binary.Morphism.Structures.IsOrderMonomorphism
d_IsOrderMonomorphism_190 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
  = ()
data T_IsOrderMonomorphism_190
  = C_constructor_228 T_IsOrderHomomorphism_144
                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Relation.Binary.Morphism.Structures.IsOrderMonomorphism.isOrderHomomorphism
d_isOrderHomomorphism_208 ::
  T_IsOrderMonomorphism_190 -> T_IsOrderHomomorphism_144
d_isOrderHomomorphism_208 v0
  = case coe v0 of
      C_constructor_228 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Morphism.Structures.IsOrderMonomorphism.injective
d_injective_210 ::
  T_IsOrderMonomorphism_190 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_210 v0
  = case coe v0 of
      C_constructor_228 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Morphism.Structures.IsOrderMonomorphism.cancel
d_cancel_212 ::
  T_IsOrderMonomorphism_190 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cancel_212 v0
  = case coe v0 of
      C_constructor_228 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Morphism.Structures.IsOrderMonomorphism._.cong
d_cong_216 ::
  T_IsOrderMonomorphism_190 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_216 v0
  = coe d_cong_160 (coe d_isOrderHomomorphism_208 (coe v0))
-- Relation.Binary.Morphism.Structures.IsOrderMonomorphism._.isRelHomomorphism
d_isRelHomomorphism_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsOrderMonomorphism_190 -> T_IsRelHomomorphism_42
d_isRelHomomorphism_218 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 ~v11 ~v12 v13
  = du_isRelHomomorphism_218 v13
du_isRelHomomorphism_218 ::
  T_IsOrderMonomorphism_190 -> T_IsRelHomomorphism_42
du_isRelHomomorphism_218 v0
  = coe
      du_isRelHomomorphism_168 (coe d_isOrderHomomorphism_208 (coe v0))
-- Relation.Binary.Morphism.Structures.IsOrderMonomorphism._.mono
d_mono_220 ::
  T_IsOrderMonomorphism_190 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_mono_220 v0
  = coe d_mono_162 (coe d_isOrderHomomorphism_208 (coe v0))
-- Relation.Binary.Morphism.Structures.IsOrderMonomorphism.Eq.isRelMonomorphism
d_isRelMonomorphism_224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsOrderMonomorphism_190 -> T_IsRelMonomorphism_66
d_isRelMonomorphism_224 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 ~v11 ~v12 v13
  = du_isRelMonomorphism_224 v13
du_isRelMonomorphism_224 ::
  T_IsOrderMonomorphism_190 -> T_IsRelMonomorphism_66
du_isRelMonomorphism_224 v0
  = coe
      C_constructor_86
      (coe
         du_isRelHomomorphism_166 (coe d_isOrderHomomorphism_208 (coe v0)))
      (coe d_injective_210 (coe v0))
-- Relation.Binary.Morphism.Structures.IsOrderMonomorphism.isRelMonomorphism
d_isRelMonomorphism_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsOrderMonomorphism_190 -> T_IsRelMonomorphism_66
d_isRelMonomorphism_226 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 ~v11 ~v12 v13
  = du_isRelMonomorphism_226 v13
du_isRelMonomorphism_226 ::
  T_IsOrderMonomorphism_190 -> T_IsRelMonomorphism_66
du_isRelMonomorphism_226 v0
  = coe
      C_constructor_86
      (coe
         du_isRelHomomorphism_168 (coe d_isOrderHomomorphism_208 (coe v0)))
      (coe d_cancel_212 (coe v0))
-- Relation.Binary.Morphism.Structures.IsOrderIsomorphism
d_IsOrderIsomorphism_248 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
  = ()
data T_IsOrderIsomorphism_248
  = C_constructor_288 T_IsOrderMonomorphism_190
                      (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Relation.Binary.Morphism.Structures.IsOrderIsomorphism.isOrderMonomorphism
d_isOrderMonomorphism_264 ::
  T_IsOrderIsomorphism_248 -> T_IsOrderMonomorphism_190
d_isOrderMonomorphism_264 v0
  = case coe v0 of
      C_constructor_288 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Morphism.Structures.IsOrderIsomorphism.surjective
d_surjective_266 ::
  T_IsOrderIsomorphism_248 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_266 v0
  = case coe v0 of
      C_constructor_288 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Morphism.Structures.IsOrderIsomorphism._.cancel
d_cancel_270 ::
  T_IsOrderIsomorphism_248 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cancel_270 v0
  = coe d_cancel_212 (coe d_isOrderMonomorphism_264 (coe v0))
-- Relation.Binary.Morphism.Structures.IsOrderIsomorphism._.cong
d_cong_272 ::
  T_IsOrderIsomorphism_248 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_272 v0
  = coe
      d_cong_160
      (coe
         d_isOrderHomomorphism_208 (coe d_isOrderMonomorphism_264 (coe v0)))
-- Relation.Binary.Morphism.Structures.IsOrderIsomorphism._.injective
d_injective_274 ::
  T_IsOrderIsomorphism_248 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_274 v0
  = coe d_injective_210 (coe d_isOrderMonomorphism_264 (coe v0))
-- Relation.Binary.Morphism.Structures.IsOrderIsomorphism._.isOrderHomomorphism
d_isOrderHomomorphism_276 ::
  T_IsOrderIsomorphism_248 -> T_IsOrderHomomorphism_144
d_isOrderHomomorphism_276 v0
  = coe
      d_isOrderHomomorphism_208 (coe d_isOrderMonomorphism_264 (coe v0))
-- Relation.Binary.Morphism.Structures.IsOrderIsomorphism._.isRelHomomorphism
d_isRelHomomorphism_278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsOrderIsomorphism_248 -> T_IsRelHomomorphism_42
d_isRelHomomorphism_278 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 ~v11 ~v12 v13
  = du_isRelHomomorphism_278 v13
du_isRelHomomorphism_278 ::
  T_IsOrderIsomorphism_248 -> T_IsRelHomomorphism_42
du_isRelHomomorphism_278 v0
  = let v1 = d_isOrderMonomorphism_264 (coe v0) in
    coe
      (coe
         du_isRelHomomorphism_168 (coe d_isOrderHomomorphism_208 (coe v1)))
-- Relation.Binary.Morphism.Structures.IsOrderIsomorphism._.isRelMonomorphism
d_isRelMonomorphism_280 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsOrderIsomorphism_248 -> T_IsRelMonomorphism_66
d_isRelMonomorphism_280 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 ~v11 ~v12 v13
  = du_isRelMonomorphism_280 v13
du_isRelMonomorphism_280 ::
  T_IsOrderIsomorphism_248 -> T_IsRelMonomorphism_66
du_isRelMonomorphism_280 v0
  = coe
      du_isRelMonomorphism_226 (coe d_isOrderMonomorphism_264 (coe v0))
-- Relation.Binary.Morphism.Structures.IsOrderIsomorphism._.mono
d_mono_282 ::
  T_IsOrderIsomorphism_248 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_mono_282 v0
  = coe
      d_mono_162
      (coe
         d_isOrderHomomorphism_208 (coe d_isOrderMonomorphism_264 (coe v0)))
-- Relation.Binary.Morphism.Structures.IsOrderIsomorphism.Eq.isRelIsomorphism
d_isRelIsomorphism_286 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsOrderIsomorphism_248 -> T_IsRelIsomorphism_98
d_isRelIsomorphism_286 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                       ~v11 ~v12 v13
  = du_isRelIsomorphism_286 v13
du_isRelIsomorphism_286 ::
  T_IsOrderIsomorphism_248 -> T_IsRelIsomorphism_98
du_isRelIsomorphism_286 v0
  = coe
      C_constructor_124
      (coe
         du_isRelMonomorphism_224 (coe d_isOrderMonomorphism_264 (coe v0)))
      (coe d_surjective_266 (coe v0))
