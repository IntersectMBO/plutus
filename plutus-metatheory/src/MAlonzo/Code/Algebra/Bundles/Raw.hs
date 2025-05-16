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

module MAlonzo.Code.Algebra.Bundles.Raw where

import Data.Text qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Algebra.Bundles.Raw.RawSuccessorSet
d_RawSuccessorSet_10 a0 a1 = ()
data T_RawSuccessorSet_10
  = C_RawSuccessorSet'46'constructor_89 (AgdaAny -> AgdaAny) AgdaAny
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
      C_RawSuccessorSet'46'constructor_89 v3 v4 -> coe v3
      _                                         -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawSuccessorSet.zero#
d_zero'35'_30 :: T_RawSuccessorSet_10 -> AgdaAny
d_zero'35'_30 v0
  = case coe v0 of
      C_RawSuccessorSet'46'constructor_89 v3 v4 -> coe v4
      _                                         -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawMagma
d_RawMagma_36 a0 a1 = ()
newtype T_RawMagma_36
  = C_RawMagma'46'constructor_341 (AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Bundles.Raw.RawMagma.Carrier
d_Carrier_48 :: T_RawMagma_36 -> ()
d_Carrier_48 = erased
-- Algebra.Bundles.Raw.RawMagma._≈_
d__'8776'__50 :: T_RawMagma_36 -> AgdaAny -> AgdaAny -> ()
d__'8776'__50 = erased
-- Algebra.Bundles.Raw.RawMagma._∙_
d__'8729'__52 :: T_RawMagma_36 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8729'__52 v0
  = case coe v0 of
      C_RawMagma'46'constructor_341 v3 -> coe v3
      _                                -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawMagma._≉_
d__'8777'__54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawMagma_36 -> AgdaAny -> AgdaAny -> ()
d__'8777'__54 = erased
-- Algebra.Bundles.Raw.RawMonoid
d_RawMonoid_64 a0 a1 = ()
data T_RawMonoid_64
  = C_RawMonoid'46'constructor_745 (AgdaAny -> AgdaAny -> AgdaAny)
                                   AgdaAny
-- Algebra.Bundles.Raw.RawMonoid.Carrier
d_Carrier_78 :: T_RawMonoid_64 -> ()
d_Carrier_78 = erased
-- Algebra.Bundles.Raw.RawMonoid._≈_
d__'8776'__80 :: T_RawMonoid_64 -> AgdaAny -> AgdaAny -> ()
d__'8776'__80 = erased
-- Algebra.Bundles.Raw.RawMonoid._∙_
d__'8729'__82 :: T_RawMonoid_64 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8729'__82 v0
  = case coe v0 of
      C_RawMonoid'46'constructor_745 v3 v4 -> coe v3
      _                                    -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawMonoid.ε
d_ε_84 :: T_RawMonoid_64 -> AgdaAny
d_ε_84 v0
  = case coe v0 of
      C_RawMonoid'46'constructor_745 v3 v4 -> coe v4
      _                                    -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawMonoid.rawMagma
d_rawMagma_86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawMonoid_64 -> T_RawMagma_36
d_rawMagma_86 ~v0 ~v1 v2 = du_rawMagma_86 v2
du_rawMagma_86 :: T_RawMonoid_64 -> T_RawMagma_36
du_rawMagma_86 v0
  = coe C_RawMagma'46'constructor_341 (d__'8729'__82 (coe v0))
-- Algebra.Bundles.Raw.RawMonoid._._≉_
d__'8777'__90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawMonoid_64 -> AgdaAny -> AgdaAny -> ()
d__'8777'__90 = erased
-- Algebra.Bundles.Raw.RawGroup
d_RawGroup_96 a0 a1 = ()
data T_RawGroup_96
  = C_RawGroup'46'constructor_1207 (AgdaAny -> AgdaAny -> AgdaAny)
                                   AgdaAny (AgdaAny -> AgdaAny)
-- Algebra.Bundles.Raw.RawGroup.Carrier
d_Carrier_112 :: T_RawGroup_96 -> ()
d_Carrier_112 = erased
-- Algebra.Bundles.Raw.RawGroup._≈_
d__'8776'__114 :: T_RawGroup_96 -> AgdaAny -> AgdaAny -> ()
d__'8776'__114 = erased
-- Algebra.Bundles.Raw.RawGroup._∙_
d__'8729'__116 :: T_RawGroup_96 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8729'__116 v0
  = case coe v0 of
      C_RawGroup'46'constructor_1207 v3 v4 v5 -> coe v3
      _                                       -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawGroup.ε
d_ε_118 :: T_RawGroup_96 -> AgdaAny
d_ε_118 v0
  = case coe v0 of
      C_RawGroup'46'constructor_1207 v3 v4 v5 -> coe v4
      _                                       -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawGroup._⁻¹
d__'8315''185'_120 :: T_RawGroup_96 -> AgdaAny -> AgdaAny
d__'8315''185'_120 v0
  = case coe v0 of
      C_RawGroup'46'constructor_1207 v3 v4 v5 -> coe v5
      _                                       -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawGroup.rawMonoid
d_rawMonoid_122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawGroup_96 -> T_RawMonoid_64
d_rawMonoid_122 ~v0 ~v1 v2 = du_rawMonoid_122 v2
du_rawMonoid_122 :: T_RawGroup_96 -> T_RawMonoid_64
du_rawMonoid_122 v0
  = coe
      C_RawMonoid'46'constructor_745 (d__'8729'__116 (coe v0))
      (d_ε_118 (coe v0))
-- Algebra.Bundles.Raw.RawGroup._._≉_
d__'8777'__126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawGroup_96 -> AgdaAny -> AgdaAny -> ()
d__'8777'__126 = erased
-- Algebra.Bundles.Raw.RawGroup._.rawMagma
d_rawMagma_128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawGroup_96 -> T_RawMagma_36
d_rawMagma_128 ~v0 ~v1 v2 = du_rawMagma_128 v2
du_rawMagma_128 :: T_RawGroup_96 -> T_RawMagma_36
du_rawMagma_128 v0
  = coe du_rawMagma_86 (coe du_rawMonoid_122 (coe v0))
-- Algebra.Bundles.Raw.RawNearSemiring
d_RawNearSemiring_134 a0 a1 = ()
data T_RawNearSemiring_134
  = C_RawNearSemiring'46'constructor_1729 (AgdaAny ->
                                           AgdaAny -> AgdaAny)
                                          (AgdaAny -> AgdaAny -> AgdaAny) AgdaAny
-- Algebra.Bundles.Raw.RawNearSemiring.Carrier
d_Carrier_150 :: T_RawNearSemiring_134 -> ()
d_Carrier_150 = erased
-- Algebra.Bundles.Raw.RawNearSemiring._≈_
d__'8776'__152 :: T_RawNearSemiring_134 -> AgdaAny -> AgdaAny -> ()
d__'8776'__152 = erased
-- Algebra.Bundles.Raw.RawNearSemiring._+_
d__'43'__154 ::
  T_RawNearSemiring_134 -> AgdaAny -> AgdaAny -> AgdaAny
d__'43'__154 v0
  = case coe v0 of
      C_RawNearSemiring'46'constructor_1729 v3 v4 v5 -> coe v3
      _                                              -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawNearSemiring._*_
d__'42'__156 ::
  T_RawNearSemiring_134 -> AgdaAny -> AgdaAny -> AgdaAny
d__'42'__156 v0
  = case coe v0 of
      C_RawNearSemiring'46'constructor_1729 v3 v4 v5 -> coe v4
      _                                              -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawNearSemiring.0#
d_0'35'_158 :: T_RawNearSemiring_134 -> AgdaAny
d_0'35'_158 v0
  = case coe v0 of
      C_RawNearSemiring'46'constructor_1729 v3 v4 v5 -> coe v5
      _                                              -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawNearSemiring.+-rawMonoid
d_'43''45'rawMonoid_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawNearSemiring_134 -> T_RawMonoid_64
d_'43''45'rawMonoid_160 ~v0 ~v1 v2 = du_'43''45'rawMonoid_160 v2
du_'43''45'rawMonoid_160 :: T_RawNearSemiring_134 -> T_RawMonoid_64
du_'43''45'rawMonoid_160 v0
  = coe
      C_RawMonoid'46'constructor_745 (d__'43'__154 (coe v0))
      (d_0'35'_158 (coe v0))
-- Algebra.Bundles.Raw.RawNearSemiring._._≉_
d__'8777'__164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawNearSemiring_134 -> AgdaAny -> AgdaAny -> ()
d__'8777'__164 = erased
-- Algebra.Bundles.Raw.RawNearSemiring._.rawMagma
d_rawMagma_166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawNearSemiring_134 -> T_RawMagma_36
d_rawMagma_166 ~v0 ~v1 v2 = du_rawMagma_166 v2
du_rawMagma_166 :: T_RawNearSemiring_134 -> T_RawMagma_36
du_rawMagma_166 v0
  = coe du_rawMagma_86 (coe du_'43''45'rawMonoid_160 (coe v0))
-- Algebra.Bundles.Raw.RawNearSemiring.*-rawMagma
d_'42''45'rawMagma_168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawNearSemiring_134 -> T_RawMagma_36
d_'42''45'rawMagma_168 ~v0 ~v1 v2 = du_'42''45'rawMagma_168 v2
du_'42''45'rawMagma_168 :: T_RawNearSemiring_134 -> T_RawMagma_36
du_'42''45'rawMagma_168 v0
  = coe C_RawMagma'46'constructor_341 (d__'42'__156 (coe v0))
-- Algebra.Bundles.Raw.RawSemiring
d_RawSemiring_174 a0 a1 = ()
data T_RawSemiring_174
  = C_RawSemiring'46'constructor_2353 (AgdaAny -> AgdaAny -> AgdaAny)
                                      (AgdaAny -> AgdaAny -> AgdaAny) AgdaAny AgdaAny
-- Algebra.Bundles.Raw.RawSemiring.Carrier
d_Carrier_192 :: T_RawSemiring_174 -> ()
d_Carrier_192 = erased
-- Algebra.Bundles.Raw.RawSemiring._≈_
d__'8776'__194 :: T_RawSemiring_174 -> AgdaAny -> AgdaAny -> ()
d__'8776'__194 = erased
-- Algebra.Bundles.Raw.RawSemiring._+_
d__'43'__196 :: T_RawSemiring_174 -> AgdaAny -> AgdaAny -> AgdaAny
d__'43'__196 v0
  = case coe v0 of
      C_RawSemiring'46'constructor_2353 v3 v4 v5 v6 -> coe v3
      _                                             -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawSemiring._*_
d__'42'__198 :: T_RawSemiring_174 -> AgdaAny -> AgdaAny -> AgdaAny
d__'42'__198 v0
  = case coe v0 of
      C_RawSemiring'46'constructor_2353 v3 v4 v5 v6 -> coe v4
      _                                             -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawSemiring.0#
d_0'35'_200 :: T_RawSemiring_174 -> AgdaAny
d_0'35'_200 v0
  = case coe v0 of
      C_RawSemiring'46'constructor_2353 v3 v4 v5 v6 -> coe v5
      _                                             -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawSemiring.1#
d_1'35'_202 :: T_RawSemiring_174 -> AgdaAny
d_1'35'_202 v0
  = case coe v0 of
      C_RawSemiring'46'constructor_2353 v3 v4 v5 v6 -> coe v6
      _                                             -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawSemiring.rawNearSemiring
d_rawNearSemiring_204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawSemiring_174 -> T_RawNearSemiring_134
d_rawNearSemiring_204 ~v0 ~v1 v2 = du_rawNearSemiring_204 v2
du_rawNearSemiring_204 ::
  T_RawSemiring_174 -> T_RawNearSemiring_134
du_rawNearSemiring_204 v0
  = coe
      C_RawNearSemiring'46'constructor_1729 (d__'43'__196 (coe v0))
      (d__'42'__198 (coe v0)) (d_0'35'_200 (coe v0))
-- Algebra.Bundles.Raw.RawSemiring._._≉_
d__'8777'__208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawSemiring_174 -> AgdaAny -> AgdaAny -> ()
d__'8777'__208 = erased
-- Algebra.Bundles.Raw.RawSemiring._.*-rawMagma
d_'42''45'rawMagma_210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawSemiring_174 -> T_RawMagma_36
d_'42''45'rawMagma_210 ~v0 ~v1 v2 = du_'42''45'rawMagma_210 v2
du_'42''45'rawMagma_210 :: T_RawSemiring_174 -> T_RawMagma_36
du_'42''45'rawMagma_210 v0
  = coe du_'42''45'rawMagma_168 (coe du_rawNearSemiring_204 (coe v0))
-- Algebra.Bundles.Raw.RawSemiring._.rawMagma
d_rawMagma_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawSemiring_174 -> T_RawMagma_36
d_rawMagma_212 ~v0 ~v1 v2 = du_rawMagma_212 v2
du_rawMagma_212 :: T_RawSemiring_174 -> T_RawMagma_36
du_rawMagma_212 v0
  = let v1 = coe du_rawNearSemiring_204 (coe v0) in
    coe (coe du_rawMagma_86 (coe du_'43''45'rawMonoid_160 (coe v1)))
-- Algebra.Bundles.Raw.RawSemiring._.+-rawMonoid
d_'43''45'rawMonoid_214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawSemiring_174 -> T_RawMonoid_64
d_'43''45'rawMonoid_214 ~v0 ~v1 v2 = du_'43''45'rawMonoid_214 v2
du_'43''45'rawMonoid_214 :: T_RawSemiring_174 -> T_RawMonoid_64
du_'43''45'rawMonoid_214 v0
  = coe
      du_'43''45'rawMonoid_160 (coe du_rawNearSemiring_204 (coe v0))
-- Algebra.Bundles.Raw.RawSemiring.*-rawMonoid
d_'42''45'rawMonoid_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawSemiring_174 -> T_RawMonoid_64
d_'42''45'rawMonoid_216 ~v0 ~v1 v2 = du_'42''45'rawMonoid_216 v2
du_'42''45'rawMonoid_216 :: T_RawSemiring_174 -> T_RawMonoid_64
du_'42''45'rawMonoid_216 v0
  = coe
      C_RawMonoid'46'constructor_745 (d__'42'__198 (coe v0))
      (d_1'35'_202 (coe v0))
-- Algebra.Bundles.Raw.RawRingWithoutOne
d_RawRingWithoutOne_222 a0 a1 = ()
data T_RawRingWithoutOne_222
  = C_RawRingWithoutOne'46'constructor_3105 (AgdaAny ->
                                             AgdaAny -> AgdaAny)
                                            (AgdaAny -> AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny)
                                            AgdaAny
-- Algebra.Bundles.Raw.RawRingWithoutOne.Carrier
d_Carrier_240 :: T_RawRingWithoutOne_222 -> ()
d_Carrier_240 = erased
-- Algebra.Bundles.Raw.RawRingWithoutOne._≈_
d__'8776'__242 ::
  T_RawRingWithoutOne_222 -> AgdaAny -> AgdaAny -> ()
d__'8776'__242 = erased
-- Algebra.Bundles.Raw.RawRingWithoutOne._+_
d__'43'__244 ::
  T_RawRingWithoutOne_222 -> AgdaAny -> AgdaAny -> AgdaAny
d__'43'__244 v0
  = case coe v0 of
      C_RawRingWithoutOne'46'constructor_3105 v3 v4 v5 v6 -> coe v3
      _                                                   -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawRingWithoutOne._*_
d__'42'__246 ::
  T_RawRingWithoutOne_222 -> AgdaAny -> AgdaAny -> AgdaAny
d__'42'__246 v0
  = case coe v0 of
      C_RawRingWithoutOne'46'constructor_3105 v3 v4 v5 v6 -> coe v4
      _                                                   -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawRingWithoutOne.-_
d_'45'__248 :: T_RawRingWithoutOne_222 -> AgdaAny -> AgdaAny
d_'45'__248 v0
  = case coe v0 of
      C_RawRingWithoutOne'46'constructor_3105 v3 v4 v5 v6 -> coe v5
      _                                                   -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawRingWithoutOne.0#
d_0'35'_250 :: T_RawRingWithoutOne_222 -> AgdaAny
d_0'35'_250 v0
  = case coe v0 of
      C_RawRingWithoutOne'46'constructor_3105 v3 v4 v5 v6 -> coe v6
      _                                                   -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawRingWithoutOne.+-rawGroup
d_'43''45'rawGroup_252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawRingWithoutOne_222 -> T_RawGroup_96
d_'43''45'rawGroup_252 ~v0 ~v1 v2 = du_'43''45'rawGroup_252 v2
du_'43''45'rawGroup_252 :: T_RawRingWithoutOne_222 -> T_RawGroup_96
du_'43''45'rawGroup_252 v0
  = coe
      C_RawGroup'46'constructor_1207 (d__'43'__244 (coe v0))
      (d_0'35'_250 (coe v0)) (d_'45'__248 (coe v0))
-- Algebra.Bundles.Raw.RawRingWithoutOne._._≉_
d__'8777'__256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawRingWithoutOne_222 -> AgdaAny -> AgdaAny -> ()
d__'8777'__256 = erased
-- Algebra.Bundles.Raw.RawRingWithoutOne._.rawMagma
d_rawMagma_258 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawRingWithoutOne_222 -> T_RawMagma_36
d_rawMagma_258 ~v0 ~v1 v2 = du_rawMagma_258 v2
du_rawMagma_258 :: T_RawRingWithoutOne_222 -> T_RawMagma_36
du_rawMagma_258 v0
  = let v1 = coe du_'43''45'rawGroup_252 (coe v0) in
    coe (coe du_rawMagma_86 (coe du_rawMonoid_122 (coe v1)))
-- Algebra.Bundles.Raw.RawRingWithoutOne._.rawMonoid
d_rawMonoid_260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawRingWithoutOne_222 -> T_RawMonoid_64
d_rawMonoid_260 ~v0 ~v1 v2 = du_rawMonoid_260 v2
du_rawMonoid_260 :: T_RawRingWithoutOne_222 -> T_RawMonoid_64
du_rawMonoid_260 v0
  = coe du_rawMonoid_122 (coe du_'43''45'rawGroup_252 (coe v0))
-- Algebra.Bundles.Raw.RawRingWithoutOne.*-rawMagma
d_'42''45'rawMagma_262 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawRingWithoutOne_222 -> T_RawMagma_36
d_'42''45'rawMagma_262 ~v0 ~v1 v2 = du_'42''45'rawMagma_262 v2
du_'42''45'rawMagma_262 :: T_RawRingWithoutOne_222 -> T_RawMagma_36
du_'42''45'rawMagma_262 v0
  = coe C_RawMagma'46'constructor_341 (d__'42'__246 (coe v0))
-- Algebra.Bundles.Raw.RawRing
d_RawRing_268 a0 a1 = ()
data T_RawRing_268
  = C_RawRing'46'constructor_3857 (AgdaAny -> AgdaAny -> AgdaAny)
                                  (AgdaAny -> AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny) AgdaAny
                                  AgdaAny
-- Algebra.Bundles.Raw.RawRing.Carrier
d_Carrier_288 :: T_RawRing_268 -> ()
d_Carrier_288 = erased
-- Algebra.Bundles.Raw.RawRing._≈_
d__'8776'__290 :: T_RawRing_268 -> AgdaAny -> AgdaAny -> ()
d__'8776'__290 = erased
-- Algebra.Bundles.Raw.RawRing._+_
d__'43'__292 :: T_RawRing_268 -> AgdaAny -> AgdaAny -> AgdaAny
d__'43'__292 v0
  = case coe v0 of
      C_RawRing'46'constructor_3857 v3 v4 v5 v6 v7 -> coe v3
      _                                            -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawRing._*_
d__'42'__294 :: T_RawRing_268 -> AgdaAny -> AgdaAny -> AgdaAny
d__'42'__294 v0
  = case coe v0 of
      C_RawRing'46'constructor_3857 v3 v4 v5 v6 v7 -> coe v4
      _                                            -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawRing.-_
d_'45'__296 :: T_RawRing_268 -> AgdaAny -> AgdaAny
d_'45'__296 v0
  = case coe v0 of
      C_RawRing'46'constructor_3857 v3 v4 v5 v6 v7 -> coe v5
      _                                            -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawRing.0#
d_0'35'_298 :: T_RawRing_268 -> AgdaAny
d_0'35'_298 v0
  = case coe v0 of
      C_RawRing'46'constructor_3857 v3 v4 v5 v6 v7 -> coe v6
      _                                            -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawRing.1#
d_1'35'_300 :: T_RawRing_268 -> AgdaAny
d_1'35'_300 v0
  = case coe v0 of
      C_RawRing'46'constructor_3857 v3 v4 v5 v6 v7 -> coe v7
      _                                            -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawRing.rawSemiring
d_rawSemiring_302 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawRing_268 -> T_RawSemiring_174
d_rawSemiring_302 ~v0 ~v1 v2 = du_rawSemiring_302 v2
du_rawSemiring_302 :: T_RawRing_268 -> T_RawSemiring_174
du_rawSemiring_302 v0
  = coe
      C_RawSemiring'46'constructor_2353 (d__'43'__292 (coe v0))
      (d__'42'__294 (coe v0)) (d_0'35'_298 (coe v0))
      (d_1'35'_300 (coe v0))
-- Algebra.Bundles.Raw.RawRing._._≉_
d__'8777'__306 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawRing_268 -> AgdaAny -> AgdaAny -> ()
d__'8777'__306 = erased
-- Algebra.Bundles.Raw.RawRing._.*-rawMagma
d_'42''45'rawMagma_308 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawRing_268 -> T_RawMagma_36
d_'42''45'rawMagma_308 ~v0 ~v1 v2 = du_'42''45'rawMagma_308 v2
du_'42''45'rawMagma_308 :: T_RawRing_268 -> T_RawMagma_36
du_'42''45'rawMagma_308 v0
  = let v1 = coe du_rawSemiring_302 (coe v0) in
    coe
      (coe du_'42''45'rawMagma_168 (coe du_rawNearSemiring_204 (coe v1)))
-- Algebra.Bundles.Raw.RawRing._.*-rawMonoid
d_'42''45'rawMonoid_310 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawRing_268 -> T_RawMonoid_64
d_'42''45'rawMonoid_310 ~v0 ~v1 v2 = du_'42''45'rawMonoid_310 v2
du_'42''45'rawMonoid_310 :: T_RawRing_268 -> T_RawMonoid_64
du_'42''45'rawMonoid_310 v0
  = coe du_'42''45'rawMonoid_216 (coe du_rawSemiring_302 (coe v0))
-- Algebra.Bundles.Raw.RawRing._.rawMagma
d_rawMagma_312 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawRing_268 -> T_RawMagma_36
d_rawMagma_312 ~v0 ~v1 v2 = du_rawMagma_312 v2
du_rawMagma_312 :: T_RawRing_268 -> T_RawMagma_36
du_rawMagma_312 v0
  = let v1 = coe du_rawSemiring_302 (coe v0) in
    coe
      (let v2 = coe du_rawNearSemiring_204 (coe v1) in
       coe (coe du_rawMagma_86 (coe du_'43''45'rawMonoid_160 (coe v2))))
-- Algebra.Bundles.Raw.RawRing._.+-rawMonoid
d_'43''45'rawMonoid_314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawRing_268 -> T_RawMonoid_64
d_'43''45'rawMonoid_314 ~v0 ~v1 v2 = du_'43''45'rawMonoid_314 v2
du_'43''45'rawMonoid_314 :: T_RawRing_268 -> T_RawMonoid_64
du_'43''45'rawMonoid_314 v0
  = let v1 = coe du_rawSemiring_302 (coe v0) in
    coe
      (coe
         du_'43''45'rawMonoid_160 (coe du_rawNearSemiring_204 (coe v1)))
-- Algebra.Bundles.Raw.RawRing.rawRingWithoutOne
d_rawRingWithoutOne_316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawRing_268 -> T_RawRingWithoutOne_222
d_rawRingWithoutOne_316 ~v0 ~v1 v2 = du_rawRingWithoutOne_316 v2
du_rawRingWithoutOne_316 ::
  T_RawRing_268 -> T_RawRingWithoutOne_222
du_rawRingWithoutOne_316 v0
  = coe
      C_RawRingWithoutOne'46'constructor_3105 (d__'43'__292 (coe v0))
      (d__'42'__294 (coe v0)) (d_'45'__296 (coe v0))
      (d_0'35'_298 (coe v0))
-- Algebra.Bundles.Raw.RawRing._.+-rawGroup
d_'43''45'rawGroup_320 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawRing_268 -> T_RawGroup_96
d_'43''45'rawGroup_320 ~v0 ~v1 v2 = du_'43''45'rawGroup_320 v2
du_'43''45'rawGroup_320 :: T_RawRing_268 -> T_RawGroup_96
du_'43''45'rawGroup_320 v0
  = coe
      du_'43''45'rawGroup_252 (coe du_rawRingWithoutOne_316 (coe v0))
-- Algebra.Bundles.Raw.RawQuasigroup
d_RawQuasigroup_326 a0 a1 = ()
data T_RawQuasigroup_326
  = C_RawQuasigroup'46'constructor_4731 (AgdaAny ->
                                         AgdaAny -> AgdaAny)
                                        (AgdaAny -> AgdaAny -> AgdaAny)
                                        (AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Bundles.Raw.RawQuasigroup.Carrier
d_Carrier_342 :: T_RawQuasigroup_326 -> ()
d_Carrier_342 = erased
-- Algebra.Bundles.Raw.RawQuasigroup._≈_
d__'8776'__344 :: T_RawQuasigroup_326 -> AgdaAny -> AgdaAny -> ()
d__'8776'__344 = erased
-- Algebra.Bundles.Raw.RawQuasigroup._∙_
d__'8729'__346 ::
  T_RawQuasigroup_326 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8729'__346 v0
  = case coe v0 of
      C_RawQuasigroup'46'constructor_4731 v3 v4 v5 -> coe v3
      _                                            -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawQuasigroup._\\_
d__'92''92'__348 ::
  T_RawQuasigroup_326 -> AgdaAny -> AgdaAny -> AgdaAny
d__'92''92'__348 v0
  = case coe v0 of
      C_RawQuasigroup'46'constructor_4731 v3 v4 v5 -> coe v4
      _                                            -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawQuasigroup._//_
d__'47''47'__350 ::
  T_RawQuasigroup_326 -> AgdaAny -> AgdaAny -> AgdaAny
d__'47''47'__350 v0
  = case coe v0 of
      C_RawQuasigroup'46'constructor_4731 v3 v4 v5 -> coe v5
      _                                            -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawQuasigroup.∙-rawMagma
d_'8729''45'rawMagma_352 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawQuasigroup_326 -> T_RawMagma_36
d_'8729''45'rawMagma_352 ~v0 ~v1 v2 = du_'8729''45'rawMagma_352 v2
du_'8729''45'rawMagma_352 :: T_RawQuasigroup_326 -> T_RawMagma_36
du_'8729''45'rawMagma_352 v0
  = coe C_RawMagma'46'constructor_341 (d__'8729'__346 (coe v0))
-- Algebra.Bundles.Raw.RawQuasigroup.\\-rawMagma
d_'92''92''45'rawMagma_354 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawQuasigroup_326 -> T_RawMagma_36
d_'92''92''45'rawMagma_354 ~v0 ~v1 v2
  = du_'92''92''45'rawMagma_354 v2
du_'92''92''45'rawMagma_354 :: T_RawQuasigroup_326 -> T_RawMagma_36
du_'92''92''45'rawMagma_354 v0
  = coe C_RawMagma'46'constructor_341 (d__'92''92'__348 (coe v0))
-- Algebra.Bundles.Raw.RawQuasigroup.//-rawMagma
d_'47''47''45'rawMagma_356 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawQuasigroup_326 -> T_RawMagma_36
d_'47''47''45'rawMagma_356 ~v0 ~v1 v2
  = du_'47''47''45'rawMagma_356 v2
du_'47''47''45'rawMagma_356 :: T_RawQuasigroup_326 -> T_RawMagma_36
du_'47''47''45'rawMagma_356 v0
  = coe C_RawMagma'46'constructor_341 (d__'47''47'__350 (coe v0))
-- Algebra.Bundles.Raw.RawQuasigroup._._≉_
d__'8777'__360 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawQuasigroup_326 -> AgdaAny -> AgdaAny -> ()
d__'8777'__360 = erased
-- Algebra.Bundles.Raw.RawLoop
d_RawLoop_366 a0 a1 = ()
data T_RawLoop_366
  = C_RawLoop'46'constructor_5465 (AgdaAny -> AgdaAny -> AgdaAny)
                                  (AgdaAny -> AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny -> AgdaAny)
                                  AgdaAny
-- Algebra.Bundles.Raw.RawLoop.Carrier
d_Carrier_384 :: T_RawLoop_366 -> ()
d_Carrier_384 = erased
-- Algebra.Bundles.Raw.RawLoop._≈_
d__'8776'__386 :: T_RawLoop_366 -> AgdaAny -> AgdaAny -> ()
d__'8776'__386 = erased
-- Algebra.Bundles.Raw.RawLoop._∙_
d__'8729'__388 :: T_RawLoop_366 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8729'__388 v0
  = case coe v0 of
      C_RawLoop'46'constructor_5465 v3 v4 v5 v6 -> coe v3
      _                                         -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawLoop._\\_
d__'92''92'__390 :: T_RawLoop_366 -> AgdaAny -> AgdaAny -> AgdaAny
d__'92''92'__390 v0
  = case coe v0 of
      C_RawLoop'46'constructor_5465 v3 v4 v5 v6 -> coe v4
      _                                         -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawLoop._//_
d__'47''47'__392 :: T_RawLoop_366 -> AgdaAny -> AgdaAny -> AgdaAny
d__'47''47'__392 v0
  = case coe v0 of
      C_RawLoop'46'constructor_5465 v3 v4 v5 v6 -> coe v5
      _                                         -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawLoop.ε
d_ε_394 :: T_RawLoop_366 -> AgdaAny
d_ε_394 v0
  = case coe v0 of
      C_RawLoop'46'constructor_5465 v3 v4 v5 v6 -> coe v6
      _                                         -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawLoop.rawQuasigroup
d_rawQuasigroup_396 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawLoop_366 -> T_RawQuasigroup_326
d_rawQuasigroup_396 ~v0 ~v1 v2 = du_rawQuasigroup_396 v2
du_rawQuasigroup_396 :: T_RawLoop_366 -> T_RawQuasigroup_326
du_rawQuasigroup_396 v0
  = coe
      C_RawQuasigroup'46'constructor_4731 (d__'8729'__388 (coe v0))
      (d__'92''92'__390 (coe v0)) (d__'47''47'__392 (coe v0))
-- Algebra.Bundles.Raw.RawLoop._._≉_
d__'8777'__400 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawLoop_366 -> AgdaAny -> AgdaAny -> ()
d__'8777'__400 = erased
-- Algebra.Bundles.Raw.RawLoop._.//-rawMagma
d_'47''47''45'rawMagma_402 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawLoop_366 -> T_RawMagma_36
d_'47''47''45'rawMagma_402 ~v0 ~v1 v2
  = du_'47''47''45'rawMagma_402 v2
du_'47''47''45'rawMagma_402 :: T_RawLoop_366 -> T_RawMagma_36
du_'47''47''45'rawMagma_402 v0
  = coe
      du_'47''47''45'rawMagma_356 (coe du_rawQuasigroup_396 (coe v0))
-- Algebra.Bundles.Raw.RawLoop._.\\-rawMagma
d_'92''92''45'rawMagma_404 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawLoop_366 -> T_RawMagma_36
d_'92''92''45'rawMagma_404 ~v0 ~v1 v2
  = du_'92''92''45'rawMagma_404 v2
du_'92''92''45'rawMagma_404 :: T_RawLoop_366 -> T_RawMagma_36
du_'92''92''45'rawMagma_404 v0
  = coe
      du_'92''92''45'rawMagma_354 (coe du_rawQuasigroup_396 (coe v0))
-- Algebra.Bundles.Raw.RawLoop._.∙-rawMagma
d_'8729''45'rawMagma_406 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawLoop_366 -> T_RawMagma_36
d_'8729''45'rawMagma_406 ~v0 ~v1 v2 = du_'8729''45'rawMagma_406 v2
du_'8729''45'rawMagma_406 :: T_RawLoop_366 -> T_RawMagma_36
du_'8729''45'rawMagma_406 v0
  = coe du_'8729''45'rawMagma_352 (coe du_rawQuasigroup_396 (coe v0))
-- Algebra.Bundles.Raw.RawKleeneAlgebra
d_RawKleeneAlgebra_412 a0 a1 = ()
data T_RawKleeneAlgebra_412
  = C_RawKleeneAlgebra'46'constructor_6153 (AgdaAny ->
                                            AgdaAny -> AgdaAny)
                                           (AgdaAny -> AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny)
                                           AgdaAny AgdaAny
-- Algebra.Bundles.Raw.RawKleeneAlgebra.Carrier
d_Carrier_432 :: T_RawKleeneAlgebra_412 -> ()
d_Carrier_432 = erased
-- Algebra.Bundles.Raw.RawKleeneAlgebra._≈_
d__'8776'__434 ::
  T_RawKleeneAlgebra_412 -> AgdaAny -> AgdaAny -> ()
d__'8776'__434 = erased
-- Algebra.Bundles.Raw.RawKleeneAlgebra._+_
d__'43'__436 ::
  T_RawKleeneAlgebra_412 -> AgdaAny -> AgdaAny -> AgdaAny
d__'43'__436 v0
  = case coe v0 of
      C_RawKleeneAlgebra'46'constructor_6153 v3 v4 v5 v6 v7 -> coe v3
      _                                                     -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawKleeneAlgebra._*_
d__'42'__438 ::
  T_RawKleeneAlgebra_412 -> AgdaAny -> AgdaAny -> AgdaAny
d__'42'__438 v0
  = case coe v0 of
      C_RawKleeneAlgebra'46'constructor_6153 v3 v4 v5 v6 v7 -> coe v4
      _                                                     -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawKleeneAlgebra._⋆
d__'8902'_440 :: T_RawKleeneAlgebra_412 -> AgdaAny -> AgdaAny
d__'8902'_440 v0
  = case coe v0 of
      C_RawKleeneAlgebra'46'constructor_6153 v3 v4 v5 v6 v7 -> coe v5
      _                                                     -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawKleeneAlgebra.0#
d_0'35'_442 :: T_RawKleeneAlgebra_412 -> AgdaAny
d_0'35'_442 v0
  = case coe v0 of
      C_RawKleeneAlgebra'46'constructor_6153 v3 v4 v5 v6 v7 -> coe v6
      _                                                     -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawKleeneAlgebra.1#
d_1'35'_444 :: T_RawKleeneAlgebra_412 -> AgdaAny
d_1'35'_444 v0
  = case coe v0 of
      C_RawKleeneAlgebra'46'constructor_6153 v3 v4 v5 v6 v7 -> coe v7
      _                                                     -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Bundles.Raw.RawKleeneAlgebra.rawSemiring
d_rawSemiring_446 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawKleeneAlgebra_412 -> T_RawSemiring_174
d_rawSemiring_446 ~v0 ~v1 v2 = du_rawSemiring_446 v2
du_rawSemiring_446 :: T_RawKleeneAlgebra_412 -> T_RawSemiring_174
du_rawSemiring_446 v0
  = coe
      C_RawSemiring'46'constructor_2353 (d__'43'__436 (coe v0))
      (d__'42'__438 (coe v0)) (d_0'35'_442 (coe v0))
      (d_1'35'_444 (coe v0))
-- Algebra.Bundles.Raw.RawKleeneAlgebra._._≉_
d__'8777'__450 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawKleeneAlgebra_412 -> AgdaAny -> AgdaAny -> ()
d__'8777'__450 = erased
-- Algebra.Bundles.Raw.RawKleeneAlgebra._.*-rawMagma
d_'42''45'rawMagma_452 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawKleeneAlgebra_412 -> T_RawMagma_36
d_'42''45'rawMagma_452 ~v0 ~v1 v2 = du_'42''45'rawMagma_452 v2
du_'42''45'rawMagma_452 :: T_RawKleeneAlgebra_412 -> T_RawMagma_36
du_'42''45'rawMagma_452 v0
  = let v1 = coe du_rawSemiring_446 (coe v0) in
    coe
      (coe du_'42''45'rawMagma_168 (coe du_rawNearSemiring_204 (coe v1)))
-- Algebra.Bundles.Raw.RawKleeneAlgebra._.*-rawMonoid
d_'42''45'rawMonoid_454 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawKleeneAlgebra_412 -> T_RawMonoid_64
d_'42''45'rawMonoid_454 ~v0 ~v1 v2 = du_'42''45'rawMonoid_454 v2
du_'42''45'rawMonoid_454 ::
  T_RawKleeneAlgebra_412 -> T_RawMonoid_64
du_'42''45'rawMonoid_454 v0
  = coe du_'42''45'rawMonoid_216 (coe du_rawSemiring_446 (coe v0))
-- Algebra.Bundles.Raw.RawKleeneAlgebra._.rawMagma
d_rawMagma_456 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawKleeneAlgebra_412 -> T_RawMagma_36
d_rawMagma_456 ~v0 ~v1 v2 = du_rawMagma_456 v2
du_rawMagma_456 :: T_RawKleeneAlgebra_412 -> T_RawMagma_36
du_rawMagma_456 v0
  = let v1 = coe du_rawSemiring_446 (coe v0) in
    coe
      (let v2 = coe du_rawNearSemiring_204 (coe v1) in
       coe (coe du_rawMagma_86 (coe du_'43''45'rawMonoid_160 (coe v2))))
-- Algebra.Bundles.Raw.RawKleeneAlgebra._.+-rawMonoid
d_'43''45'rawMonoid_458 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawKleeneAlgebra_412 -> T_RawMonoid_64
d_'43''45'rawMonoid_458 ~v0 ~v1 v2 = du_'43''45'rawMonoid_458 v2
du_'43''45'rawMonoid_458 ::
  T_RawKleeneAlgebra_412 -> T_RawMonoid_64
du_'43''45'rawMonoid_458 v0
  = let v1 = coe du_rawSemiring_446 (coe v0) in
    coe
      (coe
         du_'43''45'rawMonoid_160 (coe du_rawNearSemiring_204 (coe v1)))
