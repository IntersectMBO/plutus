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

module MAlonzo.Code.Relation.Binary.Morphism.Structures where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

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
  = C_IsRelHomomorphism'46'constructor_587 (AgdaAny ->
                                            AgdaAny -> AgdaAny -> AgdaAny)
-- Relation.Binary.Morphism.Structures.IsRelHomomorphism.cong
d_cong_52 ::
  T_IsRelHomomorphism_42 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_52 v0
  = case coe v0 of
      C_IsRelHomomorphism'46'constructor_587 v1 -> coe v1
      _                                         -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Morphism.Structures.IsRelMonomorphism
d_IsRelMonomorphism_64 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_IsRelMonomorphism_64
  = C_IsRelMonomorphism'46'constructor_1563 T_IsRelHomomorphism_42
                                            (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Relation.Binary.Morphism.Structures.IsRelMonomorphism.isHomomorphism
d_isHomomorphism_76 ::
  T_IsRelMonomorphism_64 -> T_IsRelHomomorphism_42
d_isHomomorphism_76 v0
  = case coe v0 of
      C_IsRelMonomorphism'46'constructor_1563 v1 v2 -> coe v1
      _                                             -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Morphism.Structures.IsRelMonomorphism.injective
d_injective_78 ::
  T_IsRelMonomorphism_64 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_78 v0
  = case coe v0 of
      C_IsRelMonomorphism'46'constructor_1563 v1 v2 -> coe v2
      _                                             -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Morphism.Structures.IsRelMonomorphism._.cong
d_cong_82 ::
  T_IsRelMonomorphism_64 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_82 v0 = coe d_cong_52 (coe d_isHomomorphism_76 (coe v0))
-- Relation.Binary.Morphism.Structures.IsRelIsomorphism
d_IsRelIsomorphism_94 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_IsRelIsomorphism_94
  = C_IsRelIsomorphism'46'constructor_3019 T_IsRelMonomorphism_64
                                           (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Relation.Binary.Morphism.Structures.IsRelIsomorphism.isMonomorphism
d_isMonomorphism_106 ::
  T_IsRelIsomorphism_94 -> T_IsRelMonomorphism_64
d_isMonomorphism_106 v0
  = case coe v0 of
      C_IsRelIsomorphism'46'constructor_3019 v1 v2 -> coe v1
      _                                            -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Morphism.Structures.IsRelIsomorphism.surjective
d_surjective_108 ::
  T_IsRelIsomorphism_94 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_108 v0
  = case coe v0 of
      C_IsRelIsomorphism'46'constructor_3019 v1 v2 -> coe v2
      _                                            -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Morphism.Structures.IsRelIsomorphism._.cong
d_cong_112 ::
  T_IsRelIsomorphism_94 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_112 v0
  = coe
      d_cong_52
      (coe d_isHomomorphism_76 (coe d_isMonomorphism_106 (coe v0)))
-- Relation.Binary.Morphism.Structures.IsRelIsomorphism._.injective
d_injective_114 ::
  T_IsRelIsomorphism_94 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_114 v0
  = coe d_injective_78 (coe d_isMonomorphism_106 (coe v0))
-- Relation.Binary.Morphism.Structures.IsRelIsomorphism._.isHomomorphism
d_isHomomorphism_116 ::
  T_IsRelIsomorphism_94 -> T_IsRelHomomorphism_42
d_isHomomorphism_116 v0
  = coe d_isHomomorphism_76 (coe d_isMonomorphism_106 (coe v0))
-- Relation.Binary.Morphism.Structures.IsRelIsomorphism.bijective
d_bijective_118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsRelIsomorphism_94 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bijective_118 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_bijective_118 v9
du_bijective_118 ::
  T_IsRelIsomorphism_94 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bijective_118 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe d_injective_78 (coe d_isMonomorphism_106 (coe v0)))
      (coe d_surjective_108 (coe v0))
-- Relation.Binary.Morphism.Structures.IsOrderHomomorphism
d_IsOrderHomomorphism_138 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
  = ()
data T_IsOrderHomomorphism_138
  = C_IsOrderHomomorphism'46'constructor_5435 (AgdaAny ->
                                               AgdaAny -> AgdaAny -> AgdaAny)
                                              (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Relation.Binary.Morphism.Structures.IsOrderHomomorphism.cong
d_cong_154 ::
  T_IsOrderHomomorphism_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_154 v0
  = case coe v0 of
      C_IsOrderHomomorphism'46'constructor_5435 v1 v2 -> coe v1
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Morphism.Structures.IsOrderHomomorphism.mono
d_mono_156 ::
  T_IsOrderHomomorphism_138 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_mono_156 v0
  = case coe v0 of
      C_IsOrderHomomorphism'46'constructor_5435 v1 v2 -> coe v2
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Morphism.Structures.IsOrderHomomorphism.Eq.isRelHomomorphism
d_isRelHomomorphism_160 ::
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
  T_IsOrderHomomorphism_138 -> T_IsRelHomomorphism_42
d_isRelHomomorphism_160 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 ~v11 ~v12 v13
  = du_isRelHomomorphism_160 v13
du_isRelHomomorphism_160 ::
  T_IsOrderHomomorphism_138 -> T_IsRelHomomorphism_42
du_isRelHomomorphism_160 v0
  = coe
      C_IsRelHomomorphism'46'constructor_587 (coe d_cong_154 (coe v0))
-- Relation.Binary.Morphism.Structures.IsOrderHomomorphism.isRelHomomorphism
d_isRelHomomorphism_162 ::
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
  T_IsOrderHomomorphism_138 -> T_IsRelHomomorphism_42
d_isRelHomomorphism_162 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 ~v11 ~v12 v13
  = du_isRelHomomorphism_162 v13
du_isRelHomomorphism_162 ::
  T_IsOrderHomomorphism_138 -> T_IsRelHomomorphism_42
du_isRelHomomorphism_162 v0
  = coe
      C_IsRelHomomorphism'46'constructor_587 (coe d_mono_156 (coe v0))
-- Relation.Binary.Morphism.Structures.IsOrderMonomorphism
d_IsOrderMonomorphism_182 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
  = ()
data T_IsOrderMonomorphism_182
  = C_IsOrderMonomorphism'46'constructor_9103 T_IsOrderHomomorphism_138
                                              (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                              (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Relation.Binary.Morphism.Structures.IsOrderMonomorphism.isOrderHomomorphism
d_isOrderHomomorphism_200 ::
  T_IsOrderMonomorphism_182 -> T_IsOrderHomomorphism_138
d_isOrderHomomorphism_200 v0
  = case coe v0 of
      C_IsOrderMonomorphism'46'constructor_9103 v1 v2 v3 -> coe v1
      _                                                  -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Morphism.Structures.IsOrderMonomorphism.injective
d_injective_202 ::
  T_IsOrderMonomorphism_182 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_202 v0
  = case coe v0 of
      C_IsOrderMonomorphism'46'constructor_9103 v1 v2 v3 -> coe v2
      _                                                  -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Morphism.Structures.IsOrderMonomorphism.cancel
d_cancel_204 ::
  T_IsOrderMonomorphism_182 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cancel_204 v0
  = case coe v0 of
      C_IsOrderMonomorphism'46'constructor_9103 v1 v2 v3 -> coe v3
      _                                                  -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Morphism.Structures.IsOrderMonomorphism._.cong
d_cong_208 ::
  T_IsOrderMonomorphism_182 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_208 v0
  = coe d_cong_154 (coe d_isOrderHomomorphism_200 (coe v0))
-- Relation.Binary.Morphism.Structures.IsOrderMonomorphism._.isRelHomomorphism
d_isRelHomomorphism_210 ::
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
  T_IsOrderMonomorphism_182 -> T_IsRelHomomorphism_42
d_isRelHomomorphism_210 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 ~v11 ~v12 v13
  = du_isRelHomomorphism_210 v13
du_isRelHomomorphism_210 ::
  T_IsOrderMonomorphism_182 -> T_IsRelHomomorphism_42
du_isRelHomomorphism_210 v0
  = coe
      du_isRelHomomorphism_162 (coe d_isOrderHomomorphism_200 (coe v0))
-- Relation.Binary.Morphism.Structures.IsOrderMonomorphism._.mono
d_mono_212 ::
  T_IsOrderMonomorphism_182 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_mono_212 v0
  = coe d_mono_156 (coe d_isOrderHomomorphism_200 (coe v0))
-- Relation.Binary.Morphism.Structures.IsOrderMonomorphism.Eq.isRelMonomorphism
d_isRelMonomorphism_216 ::
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
  T_IsOrderMonomorphism_182 -> T_IsRelMonomorphism_64
d_isRelMonomorphism_216 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 ~v11 ~v12 v13
  = du_isRelMonomorphism_216 v13
du_isRelMonomorphism_216 ::
  T_IsOrderMonomorphism_182 -> T_IsRelMonomorphism_64
du_isRelMonomorphism_216 v0
  = coe
      C_IsRelMonomorphism'46'constructor_1563
      (coe
         du_isRelHomomorphism_160 (coe d_isOrderHomomorphism_200 (coe v0)))
      (coe d_injective_202 (coe v0))
-- Relation.Binary.Morphism.Structures.IsOrderMonomorphism.isRelMonomorphism
d_isRelMonomorphism_218 ::
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
  T_IsOrderMonomorphism_182 -> T_IsRelMonomorphism_64
d_isRelMonomorphism_218 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 ~v11 ~v12 v13
  = du_isRelMonomorphism_218 v13
du_isRelMonomorphism_218 ::
  T_IsOrderMonomorphism_182 -> T_IsRelMonomorphism_64
du_isRelMonomorphism_218 v0
  = coe
      C_IsRelMonomorphism'46'constructor_1563
      (coe
         du_isRelHomomorphism_162 (coe d_isOrderHomomorphism_200 (coe v0)))
      (coe d_cancel_204 (coe v0))
-- Relation.Binary.Morphism.Structures.IsOrderIsomorphism
d_IsOrderIsomorphism_238 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
  = ()
data T_IsOrderIsomorphism_238
  = C_IsOrderIsomorphism'46'constructor_14201 T_IsOrderMonomorphism_182
                                              (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Relation.Binary.Morphism.Structures.IsOrderIsomorphism.isOrderMonomorphism
d_isOrderMonomorphism_254 ::
  T_IsOrderIsomorphism_238 -> T_IsOrderMonomorphism_182
d_isOrderMonomorphism_254 v0
  = case coe v0 of
      C_IsOrderIsomorphism'46'constructor_14201 v1 v2 -> coe v1
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Morphism.Structures.IsOrderIsomorphism.surjective
d_surjective_256 ::
  T_IsOrderIsomorphism_238 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_256 v0
  = case coe v0 of
      C_IsOrderIsomorphism'46'constructor_14201 v1 v2 -> coe v2
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Morphism.Structures.IsOrderIsomorphism._.cancel
d_cancel_260 ::
  T_IsOrderIsomorphism_238 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cancel_260 v0
  = coe d_cancel_204 (coe d_isOrderMonomorphism_254 (coe v0))
-- Relation.Binary.Morphism.Structures.IsOrderIsomorphism._.cong
d_cong_262 ::
  T_IsOrderIsomorphism_238 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_262 v0
  = coe
      d_cong_154
      (coe
         d_isOrderHomomorphism_200 (coe d_isOrderMonomorphism_254 (coe v0)))
-- Relation.Binary.Morphism.Structures.IsOrderIsomorphism._.injective
d_injective_264 ::
  T_IsOrderIsomorphism_238 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_264 v0
  = coe d_injective_202 (coe d_isOrderMonomorphism_254 (coe v0))
-- Relation.Binary.Morphism.Structures.IsOrderIsomorphism._.isOrderHomomorphism
d_isOrderHomomorphism_266 ::
  T_IsOrderIsomorphism_238 -> T_IsOrderHomomorphism_138
d_isOrderHomomorphism_266 v0
  = coe
      d_isOrderHomomorphism_200 (coe d_isOrderMonomorphism_254 (coe v0))
-- Relation.Binary.Morphism.Structures.IsOrderIsomorphism._.isRelHomomorphism
d_isRelHomomorphism_268 ::
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
  T_IsOrderIsomorphism_238 -> T_IsRelHomomorphism_42
d_isRelHomomorphism_268 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 ~v11 ~v12 v13
  = du_isRelHomomorphism_268 v13
du_isRelHomomorphism_268 ::
  T_IsOrderIsomorphism_238 -> T_IsRelHomomorphism_42
du_isRelHomomorphism_268 v0
  = let v1 = d_isOrderMonomorphism_254 (coe v0) in
    coe
      (coe
         du_isRelHomomorphism_162 (coe d_isOrderHomomorphism_200 (coe v1)))
-- Relation.Binary.Morphism.Structures.IsOrderIsomorphism._.isRelMonomorphism
d_isRelMonomorphism_270 ::
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
  T_IsOrderIsomorphism_238 -> T_IsRelMonomorphism_64
d_isRelMonomorphism_270 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 ~v11 ~v12 v13
  = du_isRelMonomorphism_270 v13
du_isRelMonomorphism_270 ::
  T_IsOrderIsomorphism_238 -> T_IsRelMonomorphism_64
du_isRelMonomorphism_270 v0
  = coe
      du_isRelMonomorphism_218 (coe d_isOrderMonomorphism_254 (coe v0))
-- Relation.Binary.Morphism.Structures.IsOrderIsomorphism._.mono
d_mono_272 ::
  T_IsOrderIsomorphism_238 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_mono_272 v0
  = coe
      d_mono_156
      (coe
         d_isOrderHomomorphism_200 (coe d_isOrderMonomorphism_254 (coe v0)))
-- Relation.Binary.Morphism.Structures.IsOrderIsomorphism.Eq.isRelIsomorphism
d_isRelIsomorphism_276 ::
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
  T_IsOrderIsomorphism_238 -> T_IsRelIsomorphism_94
d_isRelIsomorphism_276 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                       ~v11 ~v12 v13
  = du_isRelIsomorphism_276 v13
du_isRelIsomorphism_276 ::
  T_IsOrderIsomorphism_238 -> T_IsRelIsomorphism_94
du_isRelIsomorphism_276 v0
  = coe
      C_IsRelIsomorphism'46'constructor_3019
      (coe
         du_isRelMonomorphism_216 (coe d_isOrderMonomorphism_254 (coe v0)))
      (coe d_surjective_256 (coe v0))
