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

module MAlonzo.Code.Algebra.Bundles.Raw where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Relation.Binary.Bundles.Raw

-- Algebra.Bundles.Raw.RawSuccessorSet
d_RawSuccessorSet_10 a0 a1 = ()
data T_RawSuccessorSet_10
  = C_constructor_38 (AgdaAny -> AgdaAny) AgdaAny
-- Algebra.Bundles.Raw.RawSuccessorSet.Carrier
d_Carrier_24 :: T_RawSuccessorSet_10 -> ()
d_Carrier_24 = erased
-- Algebra.Bundles.Raw.RawSuccessorSet._≈_
d__'8776'__26 :: T_RawSuccessorSet_10 -> AgdaAny -> AgdaAny -> ()
d__'8776'__26 = erased
-- Algebra.Bundles.Raw.RawSuccessorSet.suc#
d_suc'35'_28 :: T_RawSuccessorSet_10 -> AgdaAny -> AgdaAny
d_suc'35'_28 v0
  = case coe v0 of
      C_constructor_38 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawSuccessorSet.zero#
d_zero'35'_30 :: T_RawSuccessorSet_10 -> AgdaAny
d_zero'35'_30 v0
  = case coe v0 of
      C_constructor_38 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawSuccessorSet.rawSetoid
d_rawSetoid_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawSuccessorSet_10 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_32 = erased
-- Algebra.Bundles.Raw.RawSuccessorSet._._≉_
d__'8777'__36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawSuccessorSet_10 -> AgdaAny -> AgdaAny -> ()
d__'8777'__36 = erased
-- Algebra.Bundles.Raw.RawMagma
d_RawMagma_44 a0 a1 = ()
newtype T_RawMagma_44
  = C_constructor_68 (AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Bundles.Raw.RawMagma.Carrier
d_Carrier_56 :: T_RawMagma_44 -> ()
d_Carrier_56 = erased
-- Algebra.Bundles.Raw.RawMagma._≈_
d__'8776'__58 :: T_RawMagma_44 -> AgdaAny -> AgdaAny -> ()
d__'8776'__58 = erased
-- Algebra.Bundles.Raw.RawMagma._∙_
d__'8729'__60 :: T_RawMagma_44 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8729'__60 v0
  = case coe v0 of
      C_constructor_68 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawMagma.rawSetoid
d_rawSetoid_62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawMagma_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_62 = erased
-- Algebra.Bundles.Raw.RawMagma._._≉_
d__'8777'__66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawMagma_44 -> AgdaAny -> AgdaAny -> ()
d__'8777'__66 = erased
-- Algebra.Bundles.Raw.RawMonoid
d_RawMonoid_74 a0 a1 = ()
data T_RawMonoid_74
  = C_constructor_102 (AgdaAny -> AgdaAny -> AgdaAny) AgdaAny
-- Algebra.Bundles.Raw.RawMonoid.Carrier
d_Carrier_88 :: T_RawMonoid_74 -> ()
d_Carrier_88 = erased
-- Algebra.Bundles.Raw.RawMonoid._≈_
d__'8776'__90 :: T_RawMonoid_74 -> AgdaAny -> AgdaAny -> ()
d__'8776'__90 = erased
-- Algebra.Bundles.Raw.RawMonoid._∙_
d__'8729'__92 :: T_RawMonoid_74 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8729'__92 v0
  = case coe v0 of
      C_constructor_102 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawMonoid.ε
d_ε_94 :: T_RawMonoid_74 -> AgdaAny
d_ε_94 v0
  = case coe v0 of
      C_constructor_102 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawMonoid.rawMagma
d_rawMagma_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawMonoid_74 -> T_RawMagma_44
d_rawMagma_96 ~v0 ~v1 v2 = du_rawMagma_96 v2
du_rawMagma_96 :: T_RawMonoid_74 -> T_RawMagma_44
du_rawMagma_96 v0 = coe C_constructor_68 (d__'8729'__92 (coe v0))
-- Algebra.Bundles.Raw.RawMonoid._._≉_
d__'8777'__100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawMonoid_74 -> AgdaAny -> AgdaAny -> ()
d__'8777'__100 = erased
-- Algebra.Bundles.Raw.RawGroup
d_RawGroup_108 a0 a1 = ()
data T_RawGroup_108
  = C_constructor_142 (AgdaAny -> AgdaAny -> AgdaAny) AgdaAny
                      (AgdaAny -> AgdaAny)
-- Algebra.Bundles.Raw.RawGroup.Carrier
d_Carrier_124 :: T_RawGroup_108 -> ()
d_Carrier_124 = erased
-- Algebra.Bundles.Raw.RawGroup._≈_
d__'8776'__126 :: T_RawGroup_108 -> AgdaAny -> AgdaAny -> ()
d__'8776'__126 = erased
-- Algebra.Bundles.Raw.RawGroup._∙_
d__'8729'__128 :: T_RawGroup_108 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8729'__128 v0
  = case coe v0 of
      C_constructor_142 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawGroup.ε
d_ε_130 :: T_RawGroup_108 -> AgdaAny
d_ε_130 v0
  = case coe v0 of
      C_constructor_142 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawGroup._⁻¹
d__'8315''185'_132 :: T_RawGroup_108 -> AgdaAny -> AgdaAny
d__'8315''185'_132 v0
  = case coe v0 of
      C_constructor_142 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawGroup.rawMonoid
d_rawMonoid_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawGroup_108 -> T_RawMonoid_74
d_rawMonoid_134 ~v0 ~v1 v2 = du_rawMonoid_134 v2
du_rawMonoid_134 :: T_RawGroup_108 -> T_RawMonoid_74
du_rawMonoid_134 v0
  = coe
      C_constructor_102 (d__'8729'__128 (coe v0)) (d_ε_130 (coe v0))
-- Algebra.Bundles.Raw.RawGroup._._≉_
d__'8777'__138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawGroup_108 -> AgdaAny -> AgdaAny -> ()
d__'8777'__138 = erased
-- Algebra.Bundles.Raw.RawGroup._.rawMagma
d_rawMagma_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawGroup_108 -> T_RawMagma_44
d_rawMagma_140 ~v0 ~v1 v2 = du_rawMagma_140 v2
du_rawMagma_140 :: T_RawGroup_108 -> T_RawMagma_44
du_rawMagma_140 v0
  = coe du_rawMagma_96 (coe du_rawMonoid_134 (coe v0))
-- Algebra.Bundles.Raw.RawNearSemiring
d_RawNearSemiring_148 a0 a1 = ()
data T_RawNearSemiring_148
  = C_constructor_184 (AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> AgdaAny) AgdaAny
-- Algebra.Bundles.Raw.RawNearSemiring.Carrier
d_Carrier_164 :: T_RawNearSemiring_148 -> ()
d_Carrier_164 = erased
-- Algebra.Bundles.Raw.RawNearSemiring._≈_
d__'8776'__166 :: T_RawNearSemiring_148 -> AgdaAny -> AgdaAny -> ()
d__'8776'__166 = erased
-- Algebra.Bundles.Raw.RawNearSemiring._+_
d__'43'__168 ::
  T_RawNearSemiring_148 -> AgdaAny -> AgdaAny -> AgdaAny
d__'43'__168 v0
  = case coe v0 of
      C_constructor_184 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawNearSemiring._*_
d__'42'__170 ::
  T_RawNearSemiring_148 -> AgdaAny -> AgdaAny -> AgdaAny
d__'42'__170 v0
  = case coe v0 of
      C_constructor_184 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawNearSemiring.0#
d_0'35'_172 :: T_RawNearSemiring_148 -> AgdaAny
d_0'35'_172 v0
  = case coe v0 of
      C_constructor_184 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawNearSemiring.+-rawMonoid
d_'43''45'rawMonoid_174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawNearSemiring_148 -> T_RawMonoid_74
d_'43''45'rawMonoid_174 ~v0 ~v1 v2 = du_'43''45'rawMonoid_174 v2
du_'43''45'rawMonoid_174 :: T_RawNearSemiring_148 -> T_RawMonoid_74
du_'43''45'rawMonoid_174 v0
  = coe
      C_constructor_102 (d__'43'__168 (coe v0)) (d_0'35'_172 (coe v0))
-- Algebra.Bundles.Raw.RawNearSemiring._._≉_
d__'8777'__178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawNearSemiring_148 -> AgdaAny -> AgdaAny -> ()
d__'8777'__178 = erased
-- Algebra.Bundles.Raw.RawNearSemiring._.rawMagma
d_rawMagma_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawNearSemiring_148 -> T_RawMagma_44
d_rawMagma_180 ~v0 ~v1 v2 = du_rawMagma_180 v2
du_rawMagma_180 :: T_RawNearSemiring_148 -> T_RawMagma_44
du_rawMagma_180 v0
  = coe du_rawMagma_96 (coe du_'43''45'rawMonoid_174 (coe v0))
-- Algebra.Bundles.Raw.RawNearSemiring.*-rawMagma
d_'42''45'rawMagma_182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawNearSemiring_148 -> T_RawMagma_44
d_'42''45'rawMagma_182 ~v0 ~v1 v2 = du_'42''45'rawMagma_182 v2
du_'42''45'rawMagma_182 :: T_RawNearSemiring_148 -> T_RawMagma_44
du_'42''45'rawMagma_182 v0
  = coe C_constructor_68 (d__'42'__170 (coe v0))
-- Algebra.Bundles.Raw.RawSemiring
d_RawSemiring_190 a0 a1 = ()
data T_RawSemiring_190
  = C_constructor_234 (AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> AgdaAny) AgdaAny AgdaAny
-- Algebra.Bundles.Raw.RawSemiring.Carrier
d_Carrier_208 :: T_RawSemiring_190 -> ()
d_Carrier_208 = erased
-- Algebra.Bundles.Raw.RawSemiring._≈_
d__'8776'__210 :: T_RawSemiring_190 -> AgdaAny -> AgdaAny -> ()
d__'8776'__210 = erased
-- Algebra.Bundles.Raw.RawSemiring._+_
d__'43'__212 :: T_RawSemiring_190 -> AgdaAny -> AgdaAny -> AgdaAny
d__'43'__212 v0
  = case coe v0 of
      C_constructor_234 v3 v4 v5 v6 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawSemiring._*_
d__'42'__214 :: T_RawSemiring_190 -> AgdaAny -> AgdaAny -> AgdaAny
d__'42'__214 v0
  = case coe v0 of
      C_constructor_234 v3 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawSemiring.0#
d_0'35'_216 :: T_RawSemiring_190 -> AgdaAny
d_0'35'_216 v0
  = case coe v0 of
      C_constructor_234 v3 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawSemiring.1#
d_1'35'_218 :: T_RawSemiring_190 -> AgdaAny
d_1'35'_218 v0
  = case coe v0 of
      C_constructor_234 v3 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawSemiring.rawNearSemiring
d_rawNearSemiring_220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawSemiring_190 -> T_RawNearSemiring_148
d_rawNearSemiring_220 ~v0 ~v1 v2 = du_rawNearSemiring_220 v2
du_rawNearSemiring_220 ::
  T_RawSemiring_190 -> T_RawNearSemiring_148
du_rawNearSemiring_220 v0
  = coe
      C_constructor_184 (d__'43'__212 (coe v0)) (d__'42'__214 (coe v0))
      (d_0'35'_216 (coe v0))
-- Algebra.Bundles.Raw.RawSemiring._._≉_
d__'8777'__224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawSemiring_190 -> AgdaAny -> AgdaAny -> ()
d__'8777'__224 = erased
-- Algebra.Bundles.Raw.RawSemiring._.*-rawMagma
d_'42''45'rawMagma_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawSemiring_190 -> T_RawMagma_44
d_'42''45'rawMagma_226 ~v0 ~v1 v2 = du_'42''45'rawMagma_226 v2
du_'42''45'rawMagma_226 :: T_RawSemiring_190 -> T_RawMagma_44
du_'42''45'rawMagma_226 v0
  = coe du_'42''45'rawMagma_182 (coe du_rawNearSemiring_220 (coe v0))
-- Algebra.Bundles.Raw.RawSemiring._.rawMagma
d_rawMagma_228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawSemiring_190 -> T_RawMagma_44
d_rawMagma_228 ~v0 ~v1 v2 = du_rawMagma_228 v2
du_rawMagma_228 :: T_RawSemiring_190 -> T_RawMagma_44
du_rawMagma_228 v0
  = let v1 = coe du_rawNearSemiring_220 (coe v0) in
    coe (coe du_rawMagma_96 (coe du_'43''45'rawMonoid_174 (coe v1)))
-- Algebra.Bundles.Raw.RawSemiring._.+-rawMonoid
d_'43''45'rawMonoid_230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawSemiring_190 -> T_RawMonoid_74
d_'43''45'rawMonoid_230 ~v0 ~v1 v2 = du_'43''45'rawMonoid_230 v2
du_'43''45'rawMonoid_230 :: T_RawSemiring_190 -> T_RawMonoid_74
du_'43''45'rawMonoid_230 v0
  = coe
      du_'43''45'rawMonoid_174 (coe du_rawNearSemiring_220 (coe v0))
-- Algebra.Bundles.Raw.RawSemiring.*-rawMonoid
d_'42''45'rawMonoid_232 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawSemiring_190 -> T_RawMonoid_74
d_'42''45'rawMonoid_232 ~v0 ~v1 v2 = du_'42''45'rawMonoid_232 v2
du_'42''45'rawMonoid_232 :: T_RawSemiring_190 -> T_RawMonoid_74
du_'42''45'rawMonoid_232 v0
  = coe
      C_constructor_102 (d__'42'__214 (coe v0)) (d_1'35'_218 (coe v0))
-- Algebra.Bundles.Raw.RawRingWithoutOne
d_RawRingWithoutOne_240 a0 a1 = ()
data T_RawRingWithoutOne_240
  = C_constructor_284 (AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny) AgdaAny
-- Algebra.Bundles.Raw.RawRingWithoutOne.Carrier
d_Carrier_258 :: T_RawRingWithoutOne_240 -> ()
d_Carrier_258 = erased
-- Algebra.Bundles.Raw.RawRingWithoutOne._≈_
d__'8776'__260 ::
  T_RawRingWithoutOne_240 -> AgdaAny -> AgdaAny -> ()
d__'8776'__260 = erased
-- Algebra.Bundles.Raw.RawRingWithoutOne._+_
d__'43'__262 ::
  T_RawRingWithoutOne_240 -> AgdaAny -> AgdaAny -> AgdaAny
d__'43'__262 v0
  = case coe v0 of
      C_constructor_284 v3 v4 v5 v6 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawRingWithoutOne._*_
d__'42'__264 ::
  T_RawRingWithoutOne_240 -> AgdaAny -> AgdaAny -> AgdaAny
d__'42'__264 v0
  = case coe v0 of
      C_constructor_284 v3 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawRingWithoutOne.-_
d_'45'__266 :: T_RawRingWithoutOne_240 -> AgdaAny -> AgdaAny
d_'45'__266 v0
  = case coe v0 of
      C_constructor_284 v3 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawRingWithoutOne.0#
d_0'35'_268 :: T_RawRingWithoutOne_240 -> AgdaAny
d_0'35'_268 v0
  = case coe v0 of
      C_constructor_284 v3 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawRingWithoutOne.rawNearSemiring
d_rawNearSemiring_270 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawRingWithoutOne_240 -> T_RawNearSemiring_148
d_rawNearSemiring_270 ~v0 ~v1 v2 = du_rawNearSemiring_270 v2
du_rawNearSemiring_270 ::
  T_RawRingWithoutOne_240 -> T_RawNearSemiring_148
du_rawNearSemiring_270 v0
  = coe
      C_constructor_184 (d__'43'__262 (coe v0)) (d__'42'__264 (coe v0))
      (d_0'35'_268 (coe v0))
-- Algebra.Bundles.Raw.RawRingWithoutOne._._≉_
d__'8777'__274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawRingWithoutOne_240 -> AgdaAny -> AgdaAny -> ()
d__'8777'__274 = erased
-- Algebra.Bundles.Raw.RawRingWithoutOne._.*-rawMagma
d_'42''45'rawMagma_276 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawRingWithoutOne_240 -> T_RawMagma_44
d_'42''45'rawMagma_276 ~v0 ~v1 v2 = du_'42''45'rawMagma_276 v2
du_'42''45'rawMagma_276 :: T_RawRingWithoutOne_240 -> T_RawMagma_44
du_'42''45'rawMagma_276 v0
  = coe du_'42''45'rawMagma_182 (coe du_rawNearSemiring_270 (coe v0))
-- Algebra.Bundles.Raw.RawRingWithoutOne._.rawMagma
d_rawMagma_278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawRingWithoutOne_240 -> T_RawMagma_44
d_rawMagma_278 ~v0 ~v1 v2 = du_rawMagma_278 v2
du_rawMagma_278 :: T_RawRingWithoutOne_240 -> T_RawMagma_44
du_rawMagma_278 v0
  = let v1 = coe du_rawNearSemiring_270 (coe v0) in
    coe (coe du_rawMagma_96 (coe du_'43''45'rawMonoid_174 (coe v1)))
-- Algebra.Bundles.Raw.RawRingWithoutOne._.+-rawMonoid
d_'43''45'rawMonoid_280 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawRingWithoutOne_240 -> T_RawMonoid_74
d_'43''45'rawMonoid_280 ~v0 ~v1 v2 = du_'43''45'rawMonoid_280 v2
du_'43''45'rawMonoid_280 ::
  T_RawRingWithoutOne_240 -> T_RawMonoid_74
du_'43''45'rawMonoid_280 v0
  = coe
      du_'43''45'rawMonoid_174 (coe du_rawNearSemiring_270 (coe v0))
-- Algebra.Bundles.Raw.RawRingWithoutOne.+-rawGroup
d_'43''45'rawGroup_282 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawRingWithoutOne_240 -> T_RawGroup_108
d_'43''45'rawGroup_282 ~v0 ~v1 v2 = du_'43''45'rawGroup_282 v2
du_'43''45'rawGroup_282 ::
  T_RawRingWithoutOne_240 -> T_RawGroup_108
du_'43''45'rawGroup_282 v0
  = coe
      C_constructor_142 (d__'43'__262 (coe v0)) (d_0'35'_268 (coe v0))
      (d_'45'__266 (coe v0))
-- Algebra.Bundles.Raw.RawRing
d_RawRing_290 a0 a1 = ()
data T_RawRing_290
  = C_constructor_344 (AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny) AgdaAny
                      AgdaAny
-- Algebra.Bundles.Raw.RawRing.Carrier
d_Carrier_310 :: T_RawRing_290 -> ()
d_Carrier_310 = erased
-- Algebra.Bundles.Raw.RawRing._≈_
d__'8776'__312 :: T_RawRing_290 -> AgdaAny -> AgdaAny -> ()
d__'8776'__312 = erased
-- Algebra.Bundles.Raw.RawRing._+_
d__'43'__314 :: T_RawRing_290 -> AgdaAny -> AgdaAny -> AgdaAny
d__'43'__314 v0
  = case coe v0 of
      C_constructor_344 v3 v4 v5 v6 v7 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawRing._*_
d__'42'__316 :: T_RawRing_290 -> AgdaAny -> AgdaAny -> AgdaAny
d__'42'__316 v0
  = case coe v0 of
      C_constructor_344 v3 v4 v5 v6 v7 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawRing.-_
d_'45'__318 :: T_RawRing_290 -> AgdaAny -> AgdaAny
d_'45'__318 v0
  = case coe v0 of
      C_constructor_344 v3 v4 v5 v6 v7 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawRing.0#
d_0'35'_320 :: T_RawRing_290 -> AgdaAny
d_0'35'_320 v0
  = case coe v0 of
      C_constructor_344 v3 v4 v5 v6 v7 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawRing.1#
d_1'35'_322 :: T_RawRing_290 -> AgdaAny
d_1'35'_322 v0
  = case coe v0 of
      C_constructor_344 v3 v4 v5 v6 v7 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawRing.rawSemiring
d_rawSemiring_324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawRing_290 -> T_RawSemiring_190
d_rawSemiring_324 ~v0 ~v1 v2 = du_rawSemiring_324 v2
du_rawSemiring_324 :: T_RawRing_290 -> T_RawSemiring_190
du_rawSemiring_324 v0
  = coe
      C_constructor_234 (d__'43'__314 (coe v0)) (d__'42'__316 (coe v0))
      (d_0'35'_320 (coe v0)) (d_1'35'_322 (coe v0))
-- Algebra.Bundles.Raw.RawRing._._≉_
d__'8777'__328 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawRing_290 -> AgdaAny -> AgdaAny -> ()
d__'8777'__328 = erased
-- Algebra.Bundles.Raw.RawRing._.*-rawMagma
d_'42''45'rawMagma_330 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawRing_290 -> T_RawMagma_44
d_'42''45'rawMagma_330 ~v0 ~v1 v2 = du_'42''45'rawMagma_330 v2
du_'42''45'rawMagma_330 :: T_RawRing_290 -> T_RawMagma_44
du_'42''45'rawMagma_330 v0
  = let v1 = coe du_rawSemiring_324 (coe v0) in
    coe
      (coe du_'42''45'rawMagma_182 (coe du_rawNearSemiring_220 (coe v1)))
-- Algebra.Bundles.Raw.RawRing._.*-rawMonoid
d_'42''45'rawMonoid_332 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawRing_290 -> T_RawMonoid_74
d_'42''45'rawMonoid_332 ~v0 ~v1 v2 = du_'42''45'rawMonoid_332 v2
du_'42''45'rawMonoid_332 :: T_RawRing_290 -> T_RawMonoid_74
du_'42''45'rawMonoid_332 v0
  = coe du_'42''45'rawMonoid_232 (coe du_rawSemiring_324 (coe v0))
-- Algebra.Bundles.Raw.RawRing._.rawMagma
d_rawMagma_334 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawRing_290 -> T_RawMagma_44
d_rawMagma_334 ~v0 ~v1 v2 = du_rawMagma_334 v2
du_rawMagma_334 :: T_RawRing_290 -> T_RawMagma_44
du_rawMagma_334 v0
  = let v1 = coe du_rawSemiring_324 (coe v0) in
    coe
      (let v2 = coe du_rawNearSemiring_220 (coe v1) in
       coe (coe du_rawMagma_96 (coe du_'43''45'rawMonoid_174 (coe v2))))
-- Algebra.Bundles.Raw.RawRing._.+-rawMonoid
d_'43''45'rawMonoid_336 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawRing_290 -> T_RawMonoid_74
d_'43''45'rawMonoid_336 ~v0 ~v1 v2 = du_'43''45'rawMonoid_336 v2
du_'43''45'rawMonoid_336 :: T_RawRing_290 -> T_RawMonoid_74
du_'43''45'rawMonoid_336 v0
  = let v1 = coe du_rawSemiring_324 (coe v0) in
    coe
      (coe
         du_'43''45'rawMonoid_174 (coe du_rawNearSemiring_220 (coe v1)))
-- Algebra.Bundles.Raw.RawRing.rawRingWithoutOne
d_rawRingWithoutOne_338 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawRing_290 -> T_RawRingWithoutOne_240
d_rawRingWithoutOne_338 ~v0 ~v1 v2 = du_rawRingWithoutOne_338 v2
du_rawRingWithoutOne_338 ::
  T_RawRing_290 -> T_RawRingWithoutOne_240
du_rawRingWithoutOne_338 v0
  = coe
      C_constructor_284 (d__'43'__314 (coe v0)) (d__'42'__316 (coe v0))
      (d_'45'__318 (coe v0)) (d_0'35'_320 (coe v0))
-- Algebra.Bundles.Raw.RawRing._.+-rawGroup
d_'43''45'rawGroup_342 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawRing_290 -> T_RawGroup_108
d_'43''45'rawGroup_342 ~v0 ~v1 v2 = du_'43''45'rawGroup_342 v2
du_'43''45'rawGroup_342 :: T_RawRing_290 -> T_RawGroup_108
du_'43''45'rawGroup_342 v0
  = coe
      du_'43''45'rawGroup_282 (coe du_rawRingWithoutOne_338 (coe v0))
-- Algebra.Bundles.Raw.RawQuasigroup
d_RawQuasigroup_350 a0 a1 = ()
data T_RawQuasigroup_350
  = C_constructor_386 (AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Bundles.Raw.RawQuasigroup.Carrier
d_Carrier_366 :: T_RawQuasigroup_350 -> ()
d_Carrier_366 = erased
-- Algebra.Bundles.Raw.RawQuasigroup._≈_
d__'8776'__368 :: T_RawQuasigroup_350 -> AgdaAny -> AgdaAny -> ()
d__'8776'__368 = erased
-- Algebra.Bundles.Raw.RawQuasigroup._∙_
d__'8729'__370 ::
  T_RawQuasigroup_350 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8729'__370 v0
  = case coe v0 of
      C_constructor_386 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawQuasigroup._\\_
d__'92''92'__372 ::
  T_RawQuasigroup_350 -> AgdaAny -> AgdaAny -> AgdaAny
d__'92''92'__372 v0
  = case coe v0 of
      C_constructor_386 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawQuasigroup._//_
d__'47''47'__374 ::
  T_RawQuasigroup_350 -> AgdaAny -> AgdaAny -> AgdaAny
d__'47''47'__374 v0
  = case coe v0 of
      C_constructor_386 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawQuasigroup.∙-rawMagma
d_'8729''45'rawMagma_376 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawQuasigroup_350 -> T_RawMagma_44
d_'8729''45'rawMagma_376 ~v0 ~v1 v2 = du_'8729''45'rawMagma_376 v2
du_'8729''45'rawMagma_376 :: T_RawQuasigroup_350 -> T_RawMagma_44
du_'8729''45'rawMagma_376 v0
  = coe C_constructor_68 (d__'8729'__370 (coe v0))
-- Algebra.Bundles.Raw.RawQuasigroup.\\-rawMagma
d_'92''92''45'rawMagma_378 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawQuasigroup_350 -> T_RawMagma_44
d_'92''92''45'rawMagma_378 ~v0 ~v1 v2
  = du_'92''92''45'rawMagma_378 v2
du_'92''92''45'rawMagma_378 :: T_RawQuasigroup_350 -> T_RawMagma_44
du_'92''92''45'rawMagma_378 v0
  = coe C_constructor_68 (d__'92''92'__372 (coe v0))
-- Algebra.Bundles.Raw.RawQuasigroup.//-rawMagma
d_'47''47''45'rawMagma_380 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawQuasigroup_350 -> T_RawMagma_44
d_'47''47''45'rawMagma_380 ~v0 ~v1 v2
  = du_'47''47''45'rawMagma_380 v2
du_'47''47''45'rawMagma_380 :: T_RawQuasigroup_350 -> T_RawMagma_44
du_'47''47''45'rawMagma_380 v0
  = coe C_constructor_68 (d__'47''47'__374 (coe v0))
-- Algebra.Bundles.Raw.RawQuasigroup._._≉_
d__'8777'__384 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawQuasigroup_350 -> AgdaAny -> AgdaAny -> ()
d__'8777'__384 = erased
-- Algebra.Bundles.Raw.RawLoop
d_RawLoop_392 a0 a1 = ()
data T_RawLoop_392
  = C_constructor_434 (AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny -> AgdaAny)
                      AgdaAny
-- Algebra.Bundles.Raw.RawLoop.Carrier
d_Carrier_410 :: T_RawLoop_392 -> ()
d_Carrier_410 = erased
-- Algebra.Bundles.Raw.RawLoop._≈_
d__'8776'__412 :: T_RawLoop_392 -> AgdaAny -> AgdaAny -> ()
d__'8776'__412 = erased
-- Algebra.Bundles.Raw.RawLoop._∙_
d__'8729'__414 :: T_RawLoop_392 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8729'__414 v0
  = case coe v0 of
      C_constructor_434 v3 v4 v5 v6 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawLoop._\\_
d__'92''92'__416 :: T_RawLoop_392 -> AgdaAny -> AgdaAny -> AgdaAny
d__'92''92'__416 v0
  = case coe v0 of
      C_constructor_434 v3 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawLoop._//_
d__'47''47'__418 :: T_RawLoop_392 -> AgdaAny -> AgdaAny -> AgdaAny
d__'47''47'__418 v0
  = case coe v0 of
      C_constructor_434 v3 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawLoop.ε
d_ε_420 :: T_RawLoop_392 -> AgdaAny
d_ε_420 v0
  = case coe v0 of
      C_constructor_434 v3 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawLoop.rawQuasigroup
d_rawQuasigroup_422 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawLoop_392 -> T_RawQuasigroup_350
d_rawQuasigroup_422 ~v0 ~v1 v2 = du_rawQuasigroup_422 v2
du_rawQuasigroup_422 :: T_RawLoop_392 -> T_RawQuasigroup_350
du_rawQuasigroup_422 v0
  = coe
      C_constructor_386 (d__'8729'__414 (coe v0))
      (d__'92''92'__416 (coe v0)) (d__'47''47'__418 (coe v0))
-- Algebra.Bundles.Raw.RawLoop._._≉_
d__'8777'__426 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawLoop_392 -> AgdaAny -> AgdaAny -> ()
d__'8777'__426 = erased
-- Algebra.Bundles.Raw.RawLoop._.//-rawMagma
d_'47''47''45'rawMagma_428 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawLoop_392 -> T_RawMagma_44
d_'47''47''45'rawMagma_428 ~v0 ~v1 v2
  = du_'47''47''45'rawMagma_428 v2
du_'47''47''45'rawMagma_428 :: T_RawLoop_392 -> T_RawMagma_44
du_'47''47''45'rawMagma_428 v0
  = coe
      du_'47''47''45'rawMagma_380 (coe du_rawQuasigroup_422 (coe v0))
-- Algebra.Bundles.Raw.RawLoop._.\\-rawMagma
d_'92''92''45'rawMagma_430 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawLoop_392 -> T_RawMagma_44
d_'92''92''45'rawMagma_430 ~v0 ~v1 v2
  = du_'92''92''45'rawMagma_430 v2
du_'92''92''45'rawMagma_430 :: T_RawLoop_392 -> T_RawMagma_44
du_'92''92''45'rawMagma_430 v0
  = coe
      du_'92''92''45'rawMagma_378 (coe du_rawQuasigroup_422 (coe v0))
-- Algebra.Bundles.Raw.RawLoop._.∙-rawMagma
d_'8729''45'rawMagma_432 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawLoop_392 -> T_RawMagma_44
d_'8729''45'rawMagma_432 ~v0 ~v1 v2 = du_'8729''45'rawMagma_432 v2
du_'8729''45'rawMagma_432 :: T_RawLoop_392 -> T_RawMagma_44
du_'8729''45'rawMagma_432 v0
  = coe du_'8729''45'rawMagma_376 (coe du_rawQuasigroup_422 (coe v0))
-- Algebra.Bundles.Raw.RawKleeneAlgebra
d_RawKleeneAlgebra_440 a0 a1 = ()
data T_RawKleeneAlgebra_440
  = C_constructor_488 (AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny) AgdaAny
                      AgdaAny
-- Algebra.Bundles.Raw.RawKleeneAlgebra.Carrier
d_Carrier_460 :: T_RawKleeneAlgebra_440 -> ()
d_Carrier_460 = erased
-- Algebra.Bundles.Raw.RawKleeneAlgebra._≈_
d__'8776'__462 ::
  T_RawKleeneAlgebra_440 -> AgdaAny -> AgdaAny -> ()
d__'8776'__462 = erased
-- Algebra.Bundles.Raw.RawKleeneAlgebra._+_
d__'43'__464 ::
  T_RawKleeneAlgebra_440 -> AgdaAny -> AgdaAny -> AgdaAny
d__'43'__464 v0
  = case coe v0 of
      C_constructor_488 v3 v4 v5 v6 v7 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawKleeneAlgebra._*_
d__'42'__466 ::
  T_RawKleeneAlgebra_440 -> AgdaAny -> AgdaAny -> AgdaAny
d__'42'__466 v0
  = case coe v0 of
      C_constructor_488 v3 v4 v5 v6 v7 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawKleeneAlgebra._⋆
d__'8902'_468 :: T_RawKleeneAlgebra_440 -> AgdaAny -> AgdaAny
d__'8902'_468 v0
  = case coe v0 of
      C_constructor_488 v3 v4 v5 v6 v7 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawKleeneAlgebra.0#
d_0'35'_470 :: T_RawKleeneAlgebra_440 -> AgdaAny
d_0'35'_470 v0
  = case coe v0 of
      C_constructor_488 v3 v4 v5 v6 v7 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawKleeneAlgebra.1#
d_1'35'_472 :: T_RawKleeneAlgebra_440 -> AgdaAny
d_1'35'_472 v0
  = case coe v0 of
      C_constructor_488 v3 v4 v5 v6 v7 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawKleeneAlgebra.rawSemiring
d_rawSemiring_474 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawKleeneAlgebra_440 -> T_RawSemiring_190
d_rawSemiring_474 ~v0 ~v1 v2 = du_rawSemiring_474 v2
du_rawSemiring_474 :: T_RawKleeneAlgebra_440 -> T_RawSemiring_190
du_rawSemiring_474 v0
  = coe
      C_constructor_234 (d__'43'__464 (coe v0)) (d__'42'__466 (coe v0))
      (d_0'35'_470 (coe v0)) (d_1'35'_472 (coe v0))
-- Algebra.Bundles.Raw.RawKleeneAlgebra._._≉_
d__'8777'__478 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawKleeneAlgebra_440 -> AgdaAny -> AgdaAny -> ()
d__'8777'__478 = erased
-- Algebra.Bundles.Raw.RawKleeneAlgebra._.*-rawMagma
d_'42''45'rawMagma_480 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawKleeneAlgebra_440 -> T_RawMagma_44
d_'42''45'rawMagma_480 ~v0 ~v1 v2 = du_'42''45'rawMagma_480 v2
du_'42''45'rawMagma_480 :: T_RawKleeneAlgebra_440 -> T_RawMagma_44
du_'42''45'rawMagma_480 v0
  = let v1 = coe du_rawSemiring_474 (coe v0) in
    coe
      (coe du_'42''45'rawMagma_182 (coe du_rawNearSemiring_220 (coe v1)))
-- Algebra.Bundles.Raw.RawKleeneAlgebra._.*-rawMonoid
d_'42''45'rawMonoid_482 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawKleeneAlgebra_440 -> T_RawMonoid_74
d_'42''45'rawMonoid_482 ~v0 ~v1 v2 = du_'42''45'rawMonoid_482 v2
du_'42''45'rawMonoid_482 ::
  T_RawKleeneAlgebra_440 -> T_RawMonoid_74
du_'42''45'rawMonoid_482 v0
  = coe du_'42''45'rawMonoid_232 (coe du_rawSemiring_474 (coe v0))
-- Algebra.Bundles.Raw.RawKleeneAlgebra._.rawMagma
d_rawMagma_484 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawKleeneAlgebra_440 -> T_RawMagma_44
d_rawMagma_484 ~v0 ~v1 v2 = du_rawMagma_484 v2
du_rawMagma_484 :: T_RawKleeneAlgebra_440 -> T_RawMagma_44
du_rawMagma_484 v0
  = let v1 = coe du_rawSemiring_474 (coe v0) in
    coe
      (let v2 = coe du_rawNearSemiring_220 (coe v1) in
       coe (coe du_rawMagma_96 (coe du_'43''45'rawMonoid_174 (coe v2))))
-- Algebra.Bundles.Raw.RawKleeneAlgebra._.+-rawMonoid
d_'43''45'rawMonoid_486 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawKleeneAlgebra_440 -> T_RawMonoid_74
d_'43''45'rawMonoid_486 ~v0 ~v1 v2 = du_'43''45'rawMonoid_486 v2
du_'43''45'rawMonoid_486 ::
  T_RawKleeneAlgebra_440 -> T_RawMonoid_74
du_'43''45'rawMonoid_486 v0
  = let v1 = coe du_rawSemiring_474 (coe v0) in
    coe
      (coe
         du_'43''45'rawMonoid_174 (coe du_rawNearSemiring_220 (coe v1)))
