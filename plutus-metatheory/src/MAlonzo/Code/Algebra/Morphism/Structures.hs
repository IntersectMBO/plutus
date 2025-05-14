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

module MAlonzo.Code.Algebra.Morphism.Structures where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Algebra.Bundles.Raw qualified
import MAlonzo.Code.Relation.Binary.Morphism.Structures qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Algebra.Morphism.Structures.SuccessorSetMorphisms._._≈_
d__'8776'__30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSuccessorSet_10 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSuccessorSet_10 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__30 = erased
-- Algebra.Morphism.Structures.SuccessorSetMorphisms._.Carrier
d_Carrier_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSuccessorSet_10 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSuccessorSet_10 -> ()
d_Carrier_32 = erased
-- Algebra.Morphism.Structures.SuccessorSetMorphisms._.suc#
d_suc'35'_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSuccessorSet_10 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSuccessorSet_10 ->
  AgdaAny -> AgdaAny
d_suc'35'_34 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_suc'35'_34 v4
du_suc'35'_34 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSuccessorSet_10 ->
  AgdaAny -> AgdaAny
du_suc'35'_34 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d_suc'35'_28 (coe v0)
-- Algebra.Morphism.Structures.SuccessorSetMorphisms._.zero#
d_zero'35'_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSuccessorSet_10 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSuccessorSet_10 -> AgdaAny
d_zero'35'_36 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_zero'35'_36 v4
du_zero'35'_36 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSuccessorSet_10 -> AgdaAny
du_zero'35'_36 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d_zero'35'_30 (coe v0)
-- Algebra.Morphism.Structures.SuccessorSetMorphisms._.Homomorphic₀
d_Homomorphic'8320'_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSuccessorSet_10 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSuccessorSet_10 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> ()
d_Homomorphic'8320'_50 = erased
-- Algebra.Morphism.Structures.SuccessorSetMorphisms._.Homomorphic₁
d_Homomorphic'8321'_52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSuccessorSet_10 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSuccessorSet_10 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8321'_52 = erased
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetHomomorphism
d_IsSuccessorSetHomomorphism_60 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsSuccessorSetHomomorphism_60
  = C_IsSuccessorSetHomomorphism'46'constructor_777 MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
                                                    (AgdaAny -> AgdaAny) AgdaAny
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetHomomorphism.isRelHomomorphism
d_isRelHomomorphism_70 ::
  T_IsSuccessorSetHomomorphism_60 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_70 v0
  = case coe v0 of
      C_IsSuccessorSetHomomorphism'46'constructor_777 v1 v2 v3 -> coe v1
      _                                                        -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetHomomorphism.suc#-homo
d_suc'35''45'homo_72 ::
  T_IsSuccessorSetHomomorphism_60 -> AgdaAny -> AgdaAny
d_suc'35''45'homo_72 v0
  = case coe v0 of
      C_IsSuccessorSetHomomorphism'46'constructor_777 v1 v2 v3 -> coe v2
      _                                                        -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetHomomorphism.zero#-homo
d_zero'35''45'homo_74 :: T_IsSuccessorSetHomomorphism_60 -> AgdaAny
d_zero'35''45'homo_74 v0
  = case coe v0 of
      C_IsSuccessorSetHomomorphism'46'constructor_777 v1 v2 v3 -> coe v3
      _                                                        -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetMonomorphism
d_IsSuccessorSetMonomorphism_78 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsSuccessorSetMonomorphism_78
  = C_IsSuccessorSetMonomorphism'46'constructor_1407 T_IsSuccessorSetHomomorphism_60
                                                     (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetMonomorphism.isSuccessorSetHomomorphism
d_isSuccessorSetHomomorphism_86 ::
  T_IsSuccessorSetMonomorphism_78 -> T_IsSuccessorSetHomomorphism_60
d_isSuccessorSetHomomorphism_86 v0
  = case coe v0 of
      C_IsSuccessorSetMonomorphism'46'constructor_1407 v1 v2 -> coe v1
      _                                                      -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetMonomorphism.injective
d_injective_88 ::
  T_IsSuccessorSetMonomorphism_78 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_88 v0
  = case coe v0 of
      C_IsSuccessorSetMonomorphism'46'constructor_1407 v1 v2 -> coe v2
      _                                                      -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetMonomorphism._.isRelHomomorphism
d_isRelHomomorphism_92 ::
  T_IsSuccessorSetMonomorphism_78 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_92 v0
  = coe
      d_isRelHomomorphism_70
      (coe d_isSuccessorSetHomomorphism_86 (coe v0))
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetMonomorphism._.suc#-homo
d_suc'35''45'homo_94 ::
  T_IsSuccessorSetMonomorphism_78 -> AgdaAny -> AgdaAny
d_suc'35''45'homo_94 v0
  = coe
      d_suc'35''45'homo_72 (coe d_isSuccessorSetHomomorphism_86 (coe v0))
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetMonomorphism._.zero#-homo
d_zero'35''45'homo_96 :: T_IsSuccessorSetMonomorphism_78 -> AgdaAny
d_zero'35''45'homo_96 v0
  = coe
      d_zero'35''45'homo_74
      (coe d_isSuccessorSetHomomorphism_86 (coe v0))
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetMonomorphism.isRelMonomorphism
d_isRelMonomorphism_98 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSuccessorSet_10 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSuccessorSet_10 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSuccessorSetMonomorphism_78 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_98 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_98 v7
du_isRelMonomorphism_98 ::
  T_IsSuccessorSetMonomorphism_78 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_98 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.C_IsRelMonomorphism'46'constructor_1563
      (coe
         d_isRelHomomorphism_70
         (coe d_isSuccessorSetHomomorphism_86 (coe v0)))
      (coe d_injective_88 (coe v0))
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetIsomorphism
d_IsSuccessorSetIsomorphism_102 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsSuccessorSetIsomorphism_102
  = C_IsSuccessorSetIsomorphism'46'constructor_2827 T_IsSuccessorSetMonomorphism_78
                                                    (AgdaAny ->
                                                     MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetIsomorphism.isSuccessorSetMonomorphism
d_isSuccessorSetMonomorphism_110 ::
  T_IsSuccessorSetIsomorphism_102 -> T_IsSuccessorSetMonomorphism_78
d_isSuccessorSetMonomorphism_110 v0
  = case coe v0 of
      C_IsSuccessorSetIsomorphism'46'constructor_2827 v1 v2 -> coe v1
      _                                                     -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetIsomorphism.surjective
d_surjective_112 ::
  T_IsSuccessorSetIsomorphism_102 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_112 v0
  = case coe v0 of
      C_IsSuccessorSetIsomorphism'46'constructor_2827 v1 v2 -> coe v2
      _                                                     -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetIsomorphism._.injective
d_injective_116 ::
  T_IsSuccessorSetIsomorphism_102 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_116 v0
  = coe
      d_injective_88 (coe d_isSuccessorSetMonomorphism_110 (coe v0))
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetIsomorphism._.isRelHomomorphism
d_isRelHomomorphism_118 ::
  T_IsSuccessorSetIsomorphism_102 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_118 v0
  = coe
      d_isRelHomomorphism_70
      (coe
         d_isSuccessorSetHomomorphism_86
         (coe d_isSuccessorSetMonomorphism_110 (coe v0)))
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetIsomorphism._.isRelMonomorphism
d_isRelMonomorphism_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSuccessorSet_10 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSuccessorSet_10 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSuccessorSetIsomorphism_102 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_120 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_120 v7
du_isRelMonomorphism_120 ::
  T_IsSuccessorSetIsomorphism_102 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_120 v0
  = coe
      du_isRelMonomorphism_98
      (coe d_isSuccessorSetMonomorphism_110 (coe v0))
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetIsomorphism._.isSuccessorSetHomomorphism
d_isSuccessorSetHomomorphism_122 ::
  T_IsSuccessorSetIsomorphism_102 -> T_IsSuccessorSetHomomorphism_60
d_isSuccessorSetHomomorphism_122 v0
  = coe
      d_isSuccessorSetHomomorphism_86
      (coe d_isSuccessorSetMonomorphism_110 (coe v0))
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetIsomorphism._.suc#-homo
d_suc'35''45'homo_124 ::
  T_IsSuccessorSetIsomorphism_102 -> AgdaAny -> AgdaAny
d_suc'35''45'homo_124 v0
  = coe
      d_suc'35''45'homo_72
      (coe
         d_isSuccessorSetHomomorphism_86
         (coe d_isSuccessorSetMonomorphism_110 (coe v0)))
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetIsomorphism._.zero#-homo
d_zero'35''45'homo_126 ::
  T_IsSuccessorSetIsomorphism_102 -> AgdaAny
d_zero'35''45'homo_126 v0
  = coe
      d_zero'35''45'homo_74
      (coe
         d_isSuccessorSetHomomorphism_86
         (coe d_isSuccessorSetMonomorphism_110 (coe v0)))
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetIsomorphism.isRelIsomorphism
d_isRelIsomorphism_128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSuccessorSet_10 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSuccessorSet_10 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSuccessorSetIsomorphism_102 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
d_isRelIsomorphism_128 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelIsomorphism_128 v7
du_isRelIsomorphism_128 ::
  T_IsSuccessorSetIsomorphism_102 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
du_isRelIsomorphism_128 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.C_IsRelIsomorphism'46'constructor_3019
      (coe
         du_isRelMonomorphism_98
         (coe d_isSuccessorSetMonomorphism_110 (coe v0)))
      (coe d_surjective_112 (coe v0))
-- Algebra.Morphism.Structures.MagmaMorphisms._._∙_
d__'8729'__146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'8729'__146 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du__'8729'__146 v4
du__'8729'__146 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'8729'__146 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__52 (coe v0)
-- Algebra.Morphism.Structures.MagmaMorphisms._._≈_
d__'8776'__148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__148 = erased
-- Algebra.Morphism.Structures.MagmaMorphisms._.Carrier
d_Carrier_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36 -> ()
d_Carrier_152 = erased
-- Algebra.Morphism.Structures.MagmaMorphisms._.Homomorphic₂
d_Homomorphic'8322'_170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8322'_170 = erased
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaHomomorphism
d_IsMagmaHomomorphism_176 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsMagmaHomomorphism_176
  = C_IsMagmaHomomorphism'46'constructor_4629 MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
                                              (AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaHomomorphism.isRelHomomorphism
d_isRelHomomorphism_184 ::
  T_IsMagmaHomomorphism_176 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_184 v0
  = case coe v0 of
      C_IsMagmaHomomorphism'46'constructor_4629 v1 v2 -> coe v1
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaHomomorphism.homo
d_homo_186 ::
  T_IsMagmaHomomorphism_176 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_186 v0
  = case coe v0 of
      C_IsMagmaHomomorphism'46'constructor_4629 v1 v2 -> coe v2
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaHomomorphism._.cong
d_cong_190 ::
  T_IsMagmaHomomorphism_176 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_190 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe d_isRelHomomorphism_184 (coe v0))
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaMonomorphism
d_IsMagmaMonomorphism_194 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsMagmaMonomorphism_194
  = C_IsMagmaMonomorphism'46'constructor_5763 T_IsMagmaHomomorphism_176
                                              (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_202 ::
  T_IsMagmaMonomorphism_194 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_202 v0
  = case coe v0 of
      C_IsMagmaMonomorphism'46'constructor_5763 v1 v2 -> coe v1
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaMonomorphism.injective
d_injective_204 ::
  T_IsMagmaMonomorphism_194 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_204 v0
  = case coe v0 of
      C_IsMagmaMonomorphism'46'constructor_5763 v1 v2 -> coe v2
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaMonomorphism._.homo
d_homo_208 ::
  T_IsMagmaMonomorphism_194 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_208 v0
  = coe d_homo_186 (coe d_isMagmaHomomorphism_202 (coe v0))
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaMonomorphism._.isRelHomomorphism
d_isRelHomomorphism_210 ::
  T_IsMagmaMonomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_210 v0
  = coe
      d_isRelHomomorphism_184 (coe d_isMagmaHomomorphism_202 (coe v0))
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaMonomorphism._.cong
d_cong_212 ::
  T_IsMagmaMonomorphism_194 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_212 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184 (coe d_isMagmaHomomorphism_202 (coe v0)))
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaMonomorphism.isRelMonomorphism
d_isRelMonomorphism_214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_214 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_214 v7
du_isRelMonomorphism_214 ::
  T_IsMagmaMonomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_214 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.C_IsRelMonomorphism'46'constructor_1563
      (coe
         d_isRelHomomorphism_184 (coe d_isMagmaHomomorphism_202 (coe v0)))
      (coe d_injective_204 (coe v0))
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaIsomorphism
d_IsMagmaIsomorphism_218 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsMagmaIsomorphism_218
  = C_IsMagmaIsomorphism'46'constructor_7199 T_IsMagmaMonomorphism_194
                                             (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaIsomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_226 ::
  T_IsMagmaIsomorphism_218 -> T_IsMagmaMonomorphism_194
d_isMagmaMonomorphism_226 v0
  = case coe v0 of
      C_IsMagmaIsomorphism'46'constructor_7199 v1 v2 -> coe v1
      _                                              -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaIsomorphism.surjective
d_surjective_228 ::
  T_IsMagmaIsomorphism_218 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_228 v0
  = case coe v0 of
      C_IsMagmaIsomorphism'46'constructor_7199 v1 v2 -> coe v2
      _                                              -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaIsomorphism._.homo
d_homo_232 ::
  T_IsMagmaIsomorphism_218 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_232 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_202 (coe d_isMagmaMonomorphism_226 (coe v0)))
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaIsomorphism._.injective
d_injective_234 ::
  T_IsMagmaIsomorphism_218 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_234 v0
  = coe d_injective_204 (coe d_isMagmaMonomorphism_226 (coe v0))
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaIsomorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_236 ::
  T_IsMagmaIsomorphism_218 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_236 v0
  = coe
      d_isMagmaHomomorphism_202 (coe d_isMagmaMonomorphism_226 (coe v0))
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaIsomorphism._.isRelHomomorphism
d_isRelHomomorphism_238 ::
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_238 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_202 (coe d_isMagmaMonomorphism_226 (coe v0)))
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaIsomorphism._.isRelMonomorphism
d_isRelMonomorphism_240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_240 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_240 v7
du_isRelMonomorphism_240 ::
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_240 v0
  = coe
      du_isRelMonomorphism_214 (coe d_isMagmaMonomorphism_226 (coe v0))
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaIsomorphism._.cong
d_cong_242 ::
  T_IsMagmaIsomorphism_218 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_242 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_202
            (coe d_isMagmaMonomorphism_226 (coe v0))))
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaIsomorphism.isRelIsomorphism
d_isRelIsomorphism_244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
d_isRelIsomorphism_244 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelIsomorphism_244 v7
du_isRelIsomorphism_244 ::
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
du_isRelIsomorphism_244 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.C_IsRelIsomorphism'46'constructor_3019
      (coe
         du_isRelMonomorphism_214 (coe d_isMagmaMonomorphism_226 (coe v0)))
      (coe d_surjective_228 (coe v0))
-- Algebra.Morphism.Structures.MonoidMorphisms._._≈_
d__'8776'__264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_64 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_64 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__264 = erased
-- Algebra.Morphism.Structures.MonoidMorphisms._.Carrier
d_Carrier_268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_64 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_64 -> ()
d_Carrier_268 = erased
-- Algebra.Morphism.Structures.MonoidMorphisms._.ε
d_ε_272 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_64 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_64 -> AgdaAny
d_ε_272 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_ε_272 v4
du_ε_272 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_64 -> AgdaAny
du_ε_272 v0 = coe MAlonzo.Code.Algebra.Bundles.Raw.d_ε_84 (coe v0)
-- Algebra.Morphism.Structures.MonoidMorphisms._.Homomorphic₀
d_Homomorphic'8320'_290 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_64 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_64 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> ()
d_Homomorphic'8320'_290 = erased
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaHomomorphism
d_IsMagmaHomomorphism_300 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaIsomorphism
d_IsMagmaIsomorphism_302 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaMonomorphism
d_IsMagmaMonomorphism_304 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaHomomorphism.homo
d_homo_308 ::
  T_IsMagmaHomomorphism_176 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_308 v0 = coe d_homo_186 (coe v0)
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaHomomorphism.isRelHomomorphism
d_isRelHomomorphism_310 ::
  T_IsMagmaHomomorphism_176 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_310 v0 = coe d_isRelHomomorphism_184 (coe v0)
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaHomomorphism.cong
d_cong_312 ::
  T_IsMagmaHomomorphism_176 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_312 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe d_isRelHomomorphism_184 (coe v0))
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaIsomorphism.homo
d_homo_316 ::
  T_IsMagmaIsomorphism_218 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_316 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_202 (coe d_isMagmaMonomorphism_226 (coe v0)))
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaIsomorphism.injective
d_injective_318 ::
  T_IsMagmaIsomorphism_218 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_318 v0
  = coe d_injective_204 (coe d_isMagmaMonomorphism_226 (coe v0))
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaIsomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_320 ::
  T_IsMagmaIsomorphism_218 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_320 v0
  = coe
      d_isMagmaHomomorphism_202 (coe d_isMagmaMonomorphism_226 (coe v0))
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaIsomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_322 ::
  T_IsMagmaIsomorphism_218 -> T_IsMagmaMonomorphism_194
d_isMagmaMonomorphism_322 v0
  = coe d_isMagmaMonomorphism_226 (coe v0)
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaIsomorphism.isRelHomomorphism
d_isRelHomomorphism_324 ::
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_324 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_202 (coe d_isMagmaMonomorphism_226 (coe v0)))
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaIsomorphism.isRelIsomorphism
d_isRelIsomorphism_326 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_64 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_64 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
d_isRelIsomorphism_326 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isRelIsomorphism_326
du_isRelIsomorphism_326 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
du_isRelIsomorphism_326 v0 v1 = coe du_isRelIsomorphism_244 v1
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaIsomorphism.isRelMonomorphism
d_isRelMonomorphism_328 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_64 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_64 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_328 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_328 v7
du_isRelMonomorphism_328 ::
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_328 v0
  = coe
      du_isRelMonomorphism_214 (coe d_isMagmaMonomorphism_226 (coe v0))
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaIsomorphism.surjective
d_surjective_330 ::
  T_IsMagmaIsomorphism_218 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_330 v0 = coe d_surjective_228 (coe v0)
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaIsomorphism.cong
d_cong_332 ::
  T_IsMagmaIsomorphism_218 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_332 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_202
            (coe d_isMagmaMonomorphism_226 (coe v0))))
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaMonomorphism.homo
d_homo_336 ::
  T_IsMagmaMonomorphism_194 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_336 v0
  = coe d_homo_186 (coe d_isMagmaHomomorphism_202 (coe v0))
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaMonomorphism.injective
d_injective_338 ::
  T_IsMagmaMonomorphism_194 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_338 v0 = coe d_injective_204 (coe v0)
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_340 ::
  T_IsMagmaMonomorphism_194 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_340 v0
  = coe d_isMagmaHomomorphism_202 (coe v0)
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaMonomorphism.isRelHomomorphism
d_isRelHomomorphism_342 ::
  T_IsMagmaMonomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_342 v0
  = coe
      d_isRelHomomorphism_184 (coe d_isMagmaHomomorphism_202 (coe v0))
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaMonomorphism.isRelMonomorphism
d_isRelMonomorphism_344 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_64 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_64 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_344 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isRelMonomorphism_344
du_isRelMonomorphism_344 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_344 v0 v1 = coe du_isRelMonomorphism_214 v1
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaMonomorphism.cong
d_cong_346 ::
  T_IsMagmaMonomorphism_194 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_346 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184 (coe d_isMagmaHomomorphism_202 (coe v0)))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidHomomorphism
d_IsMonoidHomomorphism_350 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsMonoidHomomorphism_350
  = C_IsMonoidHomomorphism'46'constructor_9411 T_IsMagmaHomomorphism_176
                                               AgdaAny
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidHomomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_358 ::
  T_IsMonoidHomomorphism_350 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_358 v0
  = case coe v0 of
      C_IsMonoidHomomorphism'46'constructor_9411 v1 v2 -> coe v1
      _                                                -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidHomomorphism.ε-homo
d_ε'45'homo_360 :: T_IsMonoidHomomorphism_350 -> AgdaAny
d_ε'45'homo_360 v0
  = case coe v0 of
      C_IsMonoidHomomorphism'46'constructor_9411 v1 v2 -> coe v2
      _                                                -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidHomomorphism._.homo
d_homo_364 ::
  T_IsMonoidHomomorphism_350 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_364 v0
  = coe d_homo_186 (coe d_isMagmaHomomorphism_358 (coe v0))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidHomomorphism._.isRelHomomorphism
d_isRelHomomorphism_366 ::
  T_IsMonoidHomomorphism_350 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_366 v0
  = coe
      d_isRelHomomorphism_184 (coe d_isMagmaHomomorphism_358 (coe v0))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidHomomorphism._.cong
d_cong_368 ::
  T_IsMonoidHomomorphism_350 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_368 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184 (coe d_isMagmaHomomorphism_358 (coe v0)))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidMonomorphism
d_IsMonoidMonomorphism_372 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsMonoidMonomorphism_372
  = C_IsMonoidMonomorphism'46'constructor_10237 T_IsMonoidHomomorphism_350
                                                (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidMonomorphism.isMonoidHomomorphism
d_isMonoidHomomorphism_380 ::
  T_IsMonoidMonomorphism_372 -> T_IsMonoidHomomorphism_350
d_isMonoidHomomorphism_380 v0
  = case coe v0 of
      C_IsMonoidMonomorphism'46'constructor_10237 v1 v2 -> coe v1
      _                                                 -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidMonomorphism.injective
d_injective_382 ::
  T_IsMonoidMonomorphism_372 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_382 v0
  = case coe v0 of
      C_IsMonoidMonomorphism'46'constructor_10237 v1 v2 -> coe v2
      _                                                 -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidMonomorphism._.homo
d_homo_386 ::
  T_IsMonoidMonomorphism_372 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_386 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe d_isMonoidHomomorphism_380 (coe v0)))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidMonomorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_388 ::
  T_IsMonoidMonomorphism_372 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_388 v0
  = coe
      d_isMagmaHomomorphism_358 (coe d_isMonoidHomomorphism_380 (coe v0))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidMonomorphism._.isRelHomomorphism
d_isRelHomomorphism_390 ::
  T_IsMonoidMonomorphism_372 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_390 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe d_isMonoidHomomorphism_380 (coe v0)))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidMonomorphism._.ε-homo
d_ε'45'homo_392 :: T_IsMonoidMonomorphism_372 -> AgdaAny
d_ε'45'homo_392 v0
  = coe d_ε'45'homo_360 (coe d_isMonoidHomomorphism_380 (coe v0))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidMonomorphism._.cong
d_cong_394 ::
  T_IsMonoidMonomorphism_372 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_394 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe d_isMonoidHomomorphism_380 (coe v0))))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidMonomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_396 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_64 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_64 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidMonomorphism_372 -> T_IsMagmaMonomorphism_194
d_isMagmaMonomorphism_396 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_396 v7
du_isMagmaMonomorphism_396 ::
  T_IsMonoidMonomorphism_372 -> T_IsMagmaMonomorphism_194
du_isMagmaMonomorphism_396 v0
  = coe
      C_IsMagmaMonomorphism'46'constructor_5763
      (coe
         d_isMagmaHomomorphism_358
         (coe d_isMonoidHomomorphism_380 (coe v0)))
      (coe d_injective_382 (coe v0))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidMonomorphism._.isRelMonomorphism
d_isRelMonomorphism_400 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_64 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_64 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidMonomorphism_372 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_400 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_400 v7
du_isRelMonomorphism_400 ::
  T_IsMonoidMonomorphism_372 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_400 v0
  = coe
      du_isRelMonomorphism_214 (coe du_isMagmaMonomorphism_396 (coe v0))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidIsomorphism
d_IsMonoidIsomorphism_404 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsMonoidIsomorphism_404
  = C_IsMonoidIsomorphism'46'constructor_11597 T_IsMonoidMonomorphism_372
                                               (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidIsomorphism.isMonoidMonomorphism
d_isMonoidMonomorphism_412 ::
  T_IsMonoidIsomorphism_404 -> T_IsMonoidMonomorphism_372
d_isMonoidMonomorphism_412 v0
  = case coe v0 of
      C_IsMonoidIsomorphism'46'constructor_11597 v1 v2 -> coe v1
      _                                                -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidIsomorphism.surjective
d_surjective_414 ::
  T_IsMonoidIsomorphism_404 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_414 v0
  = case coe v0 of
      C_IsMonoidIsomorphism'46'constructor_11597 v1 v2 -> coe v2
      _                                                -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidIsomorphism._.homo
d_homo_418 ::
  T_IsMonoidIsomorphism_404 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_418 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_isMonoidHomomorphism_380
            (coe d_isMonoidMonomorphism_412 (coe v0))))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidIsomorphism._.injective
d_injective_420 ::
  T_IsMonoidIsomorphism_404 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_420 v0
  = coe d_injective_382 (coe d_isMonoidMonomorphism_412 (coe v0))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidIsomorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_422 ::
  T_IsMonoidIsomorphism_404 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_422 v0
  = coe
      d_isMagmaHomomorphism_358
      (coe
         d_isMonoidHomomorphism_380
         (coe d_isMonoidMonomorphism_412 (coe v0)))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidIsomorphism._.isMagmaMonomorphism
d_isMagmaMonomorphism_424 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_64 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_64 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_404 -> T_IsMagmaMonomorphism_194
d_isMagmaMonomorphism_424 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_424 v7
du_isMagmaMonomorphism_424 ::
  T_IsMonoidIsomorphism_404 -> T_IsMagmaMonomorphism_194
du_isMagmaMonomorphism_424 v0
  = coe
      du_isMagmaMonomorphism_396
      (coe d_isMonoidMonomorphism_412 (coe v0))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidIsomorphism._.isMonoidHomomorphism
d_isMonoidHomomorphism_426 ::
  T_IsMonoidIsomorphism_404 -> T_IsMonoidHomomorphism_350
d_isMonoidHomomorphism_426 v0
  = coe
      d_isMonoidHomomorphism_380
      (coe d_isMonoidMonomorphism_412 (coe v0))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidIsomorphism._.isRelHomomorphism
d_isRelHomomorphism_428 ::
  T_IsMonoidIsomorphism_404 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_428 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_isMonoidHomomorphism_380
            (coe d_isMonoidMonomorphism_412 (coe v0))))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidIsomorphism._.isRelMonomorphism
d_isRelMonomorphism_430 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_64 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_64 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_404 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_430 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_430 v7
du_isRelMonomorphism_430 ::
  T_IsMonoidIsomorphism_404 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_430 v0
  = let v1 = d_isMonoidMonomorphism_412 (coe v0) in
    coe
      (coe
         du_isRelMonomorphism_214 (coe du_isMagmaMonomorphism_396 (coe v1)))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidIsomorphism._.ε-homo
d_ε'45'homo_432 :: T_IsMonoidIsomorphism_404 -> AgdaAny
d_ε'45'homo_432 v0
  = coe
      d_ε'45'homo_360
      (coe
         d_isMonoidHomomorphism_380
         (coe d_isMonoidMonomorphism_412 (coe v0)))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidIsomorphism._.cong
d_cong_434 ::
  T_IsMonoidIsomorphism_404 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_434 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe
               d_isMonoidHomomorphism_380
               (coe d_isMonoidMonomorphism_412 (coe v0)))))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidIsomorphism.isMagmaIsomorphism
d_isMagmaIsomorphism_436 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_64 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_64 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_404 -> T_IsMagmaIsomorphism_218
d_isMagmaIsomorphism_436 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaIsomorphism_436 v7
du_isMagmaIsomorphism_436 ::
  T_IsMonoidIsomorphism_404 -> T_IsMagmaIsomorphism_218
du_isMagmaIsomorphism_436 v0
  = coe
      C_IsMagmaIsomorphism'46'constructor_7199
      (coe
         du_isMagmaMonomorphism_396
         (coe d_isMonoidMonomorphism_412 (coe v0)))
      (coe d_surjective_414 (coe v0))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidIsomorphism._.isRelIsomorphism
d_isRelIsomorphism_440 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_64 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_64 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_404 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
d_isRelIsomorphism_440 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelIsomorphism_440 v7
du_isRelIsomorphism_440 ::
  T_IsMonoidIsomorphism_404 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
du_isRelIsomorphism_440 v0
  = coe
      du_isRelIsomorphism_244 (coe du_isMagmaIsomorphism_436 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms._._⁻¹
d__'8315''185'_458 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  AgdaAny -> AgdaAny
d__'8315''185'_458 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du__'8315''185'_458 v4
du__'8315''185'_458 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  AgdaAny -> AgdaAny
du__'8315''185'_458 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8315''185'_120 (coe v0)
-- Algebra.Morphism.Structures.GroupMorphisms._._≈_
d__'8776'__462 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__462 = erased
-- Algebra.Morphism.Structures.GroupMorphisms._.Carrier
d_Carrier_466 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 -> ()
d_Carrier_466 = erased
-- Algebra.Morphism.Structures.GroupMorphisms._.Homomorphic₁
d_Homomorphic'8321'_496 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8321'_496 = erased
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaHomomorphism
d_IsMagmaHomomorphism_504 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaIsomorphism
d_IsMagmaIsomorphism_506 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaMonomorphism
d_IsMagmaMonomorphism_508 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaHomomorphism.homo
d_homo_512 ::
  T_IsMagmaHomomorphism_176 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_512 v0 = coe d_homo_186 (coe v0)
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaHomomorphism.isRelHomomorphism
d_isRelHomomorphism_514 ::
  T_IsMagmaHomomorphism_176 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_514 v0 = coe d_isRelHomomorphism_184 (coe v0)
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaHomomorphism.cong
d_cong_516 ::
  T_IsMagmaHomomorphism_176 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_516 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe d_isRelHomomorphism_184 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaIsomorphism.homo
d_homo_520 ::
  T_IsMagmaIsomorphism_218 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_520 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_202 (coe d_isMagmaMonomorphism_226 (coe v0)))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaIsomorphism.injective
d_injective_522 ::
  T_IsMagmaIsomorphism_218 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_522 v0
  = coe d_injective_204 (coe d_isMagmaMonomorphism_226 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaIsomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_524 ::
  T_IsMagmaIsomorphism_218 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_524 v0
  = coe
      d_isMagmaHomomorphism_202 (coe d_isMagmaMonomorphism_226 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaIsomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_526 ::
  T_IsMagmaIsomorphism_218 -> T_IsMagmaMonomorphism_194
d_isMagmaMonomorphism_526 v0
  = coe d_isMagmaMonomorphism_226 (coe v0)
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaIsomorphism.isRelHomomorphism
d_isRelHomomorphism_528 ::
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_528 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_202 (coe d_isMagmaMonomorphism_226 (coe v0)))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaIsomorphism.isRelIsomorphism
d_isRelIsomorphism_530 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
d_isRelIsomorphism_530 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isRelIsomorphism_530
du_isRelIsomorphism_530 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
du_isRelIsomorphism_530 v0 v1 = coe du_isRelIsomorphism_244 v1
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaIsomorphism.isRelMonomorphism
d_isRelMonomorphism_532 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_532 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_532 v7
du_isRelMonomorphism_532 ::
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_532 v0
  = coe
      du_isRelMonomorphism_214 (coe d_isMagmaMonomorphism_226 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaIsomorphism.surjective
d_surjective_534 ::
  T_IsMagmaIsomorphism_218 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_534 v0 = coe d_surjective_228 (coe v0)
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaIsomorphism.cong
d_cong_536 ::
  T_IsMagmaIsomorphism_218 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_536 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_202
            (coe d_isMagmaMonomorphism_226 (coe v0))))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaMonomorphism.homo
d_homo_540 ::
  T_IsMagmaMonomorphism_194 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_540 v0
  = coe d_homo_186 (coe d_isMagmaHomomorphism_202 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaMonomorphism.injective
d_injective_542 ::
  T_IsMagmaMonomorphism_194 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_542 v0 = coe d_injective_204 (coe v0)
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_544 ::
  T_IsMagmaMonomorphism_194 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_544 v0
  = coe d_isMagmaHomomorphism_202 (coe v0)
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaMonomorphism.isRelHomomorphism
d_isRelHomomorphism_546 ::
  T_IsMagmaMonomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_546 v0
  = coe
      d_isRelHomomorphism_184 (coe d_isMagmaHomomorphism_202 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaMonomorphism.isRelMonomorphism
d_isRelMonomorphism_548 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_548 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isRelMonomorphism_548
du_isRelMonomorphism_548 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_548 v0 v1 = coe du_isRelMonomorphism_214 v1
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaMonomorphism.cong
d_cong_550 ::
  T_IsMagmaMonomorphism_194 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_550 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184 (coe d_isMagmaHomomorphism_202 (coe v0)))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidHomomorphism
d_IsMonoidHomomorphism_554 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidIsomorphism
d_IsMonoidIsomorphism_556 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidMonomorphism
d_IsMonoidMonomorphism_558 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidHomomorphism.homo
d_homo_562 ::
  T_IsMonoidHomomorphism_350 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_562 v0
  = coe d_homo_186 (coe d_isMagmaHomomorphism_358 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidHomomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_564 ::
  T_IsMonoidHomomorphism_350 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_564 v0
  = coe d_isMagmaHomomorphism_358 (coe v0)
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidHomomorphism.isRelHomomorphism
d_isRelHomomorphism_566 ::
  T_IsMonoidHomomorphism_350 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_566 v0
  = coe
      d_isRelHomomorphism_184 (coe d_isMagmaHomomorphism_358 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidHomomorphism.ε-homo
d_ε'45'homo_568 :: T_IsMonoidHomomorphism_350 -> AgdaAny
d_ε'45'homo_568 v0 = coe d_ε'45'homo_360 (coe v0)
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidHomomorphism.cong
d_cong_570 ::
  T_IsMonoidHomomorphism_350 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_570 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184 (coe d_isMagmaHomomorphism_358 (coe v0)))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidIsomorphism.homo
d_homo_574 ::
  T_IsMonoidIsomorphism_404 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_574 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_isMonoidHomomorphism_380
            (coe d_isMonoidMonomorphism_412 (coe v0))))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidIsomorphism.injective
d_injective_576 ::
  T_IsMonoidIsomorphism_404 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_576 v0
  = coe d_injective_382 (coe d_isMonoidMonomorphism_412 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidIsomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_578 ::
  T_IsMonoidIsomorphism_404 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_578 v0
  = coe
      d_isMagmaHomomorphism_358
      (coe
         d_isMonoidHomomorphism_380
         (coe d_isMonoidMonomorphism_412 (coe v0)))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidIsomorphism.isMagmaIsomorphism
d_isMagmaIsomorphism_580 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_404 -> T_IsMagmaIsomorphism_218
d_isMagmaIsomorphism_580 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isMagmaIsomorphism_580
du_isMagmaIsomorphism_580 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_404 -> T_IsMagmaIsomorphism_218
du_isMagmaIsomorphism_580 v0 v1 = coe du_isMagmaIsomorphism_436 v1
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidIsomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_582 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_404 -> T_IsMagmaMonomorphism_194
d_isMagmaMonomorphism_582 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_582 v7
du_isMagmaMonomorphism_582 ::
  T_IsMonoidIsomorphism_404 -> T_IsMagmaMonomorphism_194
du_isMagmaMonomorphism_582 v0
  = coe
      du_isMagmaMonomorphism_396
      (coe d_isMonoidMonomorphism_412 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidIsomorphism.isMonoidHomomorphism
d_isMonoidHomomorphism_584 ::
  T_IsMonoidIsomorphism_404 -> T_IsMonoidHomomorphism_350
d_isMonoidHomomorphism_584 v0
  = coe
      d_isMonoidHomomorphism_380
      (coe d_isMonoidMonomorphism_412 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidIsomorphism.isMonoidMonomorphism
d_isMonoidMonomorphism_586 ::
  T_IsMonoidIsomorphism_404 -> T_IsMonoidMonomorphism_372
d_isMonoidMonomorphism_586 v0
  = coe d_isMonoidMonomorphism_412 (coe v0)
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidIsomorphism.isRelHomomorphism
d_isRelHomomorphism_588 ::
  T_IsMonoidIsomorphism_404 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_588 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_isMonoidHomomorphism_380
            (coe d_isMonoidMonomorphism_412 (coe v0))))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidIsomorphism.isRelIsomorphism
d_isRelIsomorphism_590 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_404 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
d_isRelIsomorphism_590 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelIsomorphism_590 v7
du_isRelIsomorphism_590 ::
  T_IsMonoidIsomorphism_404 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
du_isRelIsomorphism_590 v0
  = coe
      du_isRelIsomorphism_244 (coe du_isMagmaIsomorphism_436 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidIsomorphism.isRelMonomorphism
d_isRelMonomorphism_592 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_404 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_592 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_592 v7
du_isRelMonomorphism_592 ::
  T_IsMonoidIsomorphism_404 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_592 v0
  = let v1 = d_isMonoidMonomorphism_412 (coe v0) in
    coe
      (coe
         du_isRelMonomorphism_214 (coe du_isMagmaMonomorphism_396 (coe v1)))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidIsomorphism.surjective
d_surjective_594 ::
  T_IsMonoidIsomorphism_404 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_594 v0 = coe d_surjective_414 (coe v0)
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidIsomorphism.ε-homo
d_ε'45'homo_596 :: T_IsMonoidIsomorphism_404 -> AgdaAny
d_ε'45'homo_596 v0
  = coe
      d_ε'45'homo_360
      (coe
         d_isMonoidHomomorphism_380
         (coe d_isMonoidMonomorphism_412 (coe v0)))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidIsomorphism.cong
d_cong_598 ::
  T_IsMonoidIsomorphism_404 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_598 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe
               d_isMonoidHomomorphism_380
               (coe d_isMonoidMonomorphism_412 (coe v0)))))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidMonomorphism.homo
d_homo_602 ::
  T_IsMonoidMonomorphism_372 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_602 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe d_isMonoidHomomorphism_380 (coe v0)))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidMonomorphism.injective
d_injective_604 ::
  T_IsMonoidMonomorphism_372 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_604 v0 = coe d_injective_382 (coe v0)
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_606 ::
  T_IsMonoidMonomorphism_372 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_606 v0
  = coe
      d_isMagmaHomomorphism_358 (coe d_isMonoidHomomorphism_380 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidMonomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_608 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidMonomorphism_372 -> T_IsMagmaMonomorphism_194
d_isMagmaMonomorphism_608 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isMagmaMonomorphism_608
du_isMagmaMonomorphism_608 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidMonomorphism_372 -> T_IsMagmaMonomorphism_194
du_isMagmaMonomorphism_608 v0 v1
  = coe du_isMagmaMonomorphism_396 v1
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidMonomorphism.isMonoidHomomorphism
d_isMonoidHomomorphism_610 ::
  T_IsMonoidMonomorphism_372 -> T_IsMonoidHomomorphism_350
d_isMonoidHomomorphism_610 v0
  = coe d_isMonoidHomomorphism_380 (coe v0)
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidMonomorphism.isRelHomomorphism
d_isRelHomomorphism_612 ::
  T_IsMonoidMonomorphism_372 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_612 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe d_isMonoidHomomorphism_380 (coe v0)))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidMonomorphism.isRelMonomorphism
d_isRelMonomorphism_614 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidMonomorphism_372 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_614 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_614 v7
du_isRelMonomorphism_614 ::
  T_IsMonoidMonomorphism_372 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_614 v0
  = coe
      du_isRelMonomorphism_214 (coe du_isMagmaMonomorphism_396 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidMonomorphism.ε-homo
d_ε'45'homo_616 :: T_IsMonoidMonomorphism_372 -> AgdaAny
d_ε'45'homo_616 v0
  = coe d_ε'45'homo_360 (coe d_isMonoidHomomorphism_380 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidMonomorphism.cong
d_cong_618 ::
  T_IsMonoidMonomorphism_372 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_618 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe d_isMonoidHomomorphism_380 (coe v0))))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupHomomorphism
d_IsGroupHomomorphism_622 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsGroupHomomorphism_622
  = C_IsGroupHomomorphism'46'constructor_14585 T_IsMonoidHomomorphism_350
                                               (AgdaAny -> AgdaAny)
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupHomomorphism.isMonoidHomomorphism
d_isMonoidHomomorphism_630 ::
  T_IsGroupHomomorphism_622 -> T_IsMonoidHomomorphism_350
d_isMonoidHomomorphism_630 v0
  = case coe v0 of
      C_IsGroupHomomorphism'46'constructor_14585 v1 v2 -> coe v1
      _                                                -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupHomomorphism.⁻¹-homo
d_'8315''185''45'homo_632 ::
  T_IsGroupHomomorphism_622 -> AgdaAny -> AgdaAny
d_'8315''185''45'homo_632 v0
  = case coe v0 of
      C_IsGroupHomomorphism'46'constructor_14585 v1 v2 -> coe v2
      _                                                -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupHomomorphism._.homo
d_homo_636 ::
  T_IsGroupHomomorphism_622 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_636 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe d_isMonoidHomomorphism_630 (coe v0)))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupHomomorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_638 ::
  T_IsGroupHomomorphism_622 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_638 v0
  = coe
      d_isMagmaHomomorphism_358 (coe d_isMonoidHomomorphism_630 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupHomomorphism._.isRelHomomorphism
d_isRelHomomorphism_640 ::
  T_IsGroupHomomorphism_622 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_640 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe d_isMonoidHomomorphism_630 (coe v0)))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupHomomorphism._.ε-homo
d_ε'45'homo_642 :: T_IsGroupHomomorphism_622 -> AgdaAny
d_ε'45'homo_642 v0
  = coe d_ε'45'homo_360 (coe d_isMonoidHomomorphism_630 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupHomomorphism._.cong
d_cong_644 ::
  T_IsGroupHomomorphism_622 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_644 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe d_isMonoidHomomorphism_630 (coe v0))))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupMonomorphism
d_IsGroupMonomorphism_648 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsGroupMonomorphism_648
  = C_IsGroupMonomorphism'46'constructor_15537 T_IsGroupHomomorphism_622
                                               (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupMonomorphism.isGroupHomomorphism
d_isGroupHomomorphism_656 ::
  T_IsGroupMonomorphism_648 -> T_IsGroupHomomorphism_622
d_isGroupHomomorphism_656 v0
  = case coe v0 of
      C_IsGroupMonomorphism'46'constructor_15537 v1 v2 -> coe v1
      _                                                -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupMonomorphism.injective
d_injective_658 ::
  T_IsGroupMonomorphism_648 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_658 v0
  = case coe v0 of
      C_IsGroupMonomorphism'46'constructor_15537 v1 v2 -> coe v2
      _                                                -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupMonomorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_662 ::
  T_IsGroupMonomorphism_648 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_662 v0
  = coe
      d_isMagmaHomomorphism_358
      (coe
         d_isMonoidHomomorphism_630
         (coe d_isGroupHomomorphism_656 (coe v0)))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupMonomorphism._.isMonoidHomomorphism
d_isMonoidHomomorphism_664 ::
  T_IsGroupMonomorphism_648 -> T_IsMonoidHomomorphism_350
d_isMonoidHomomorphism_664 v0
  = coe
      d_isMonoidHomomorphism_630 (coe d_isGroupHomomorphism_656 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupMonomorphism._.isRelHomomorphism
d_isRelHomomorphism_666 ::
  T_IsGroupMonomorphism_648 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_666 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_isMonoidHomomorphism_630
            (coe d_isGroupHomomorphism_656 (coe v0))))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupMonomorphism._.ε-homo
d_ε'45'homo_668 :: T_IsGroupMonomorphism_648 -> AgdaAny
d_ε'45'homo_668 v0
  = coe
      d_ε'45'homo_360
      (coe
         d_isMonoidHomomorphism_630
         (coe d_isGroupHomomorphism_656 (coe v0)))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupMonomorphism._.⁻¹-homo
d_'8315''185''45'homo_670 ::
  T_IsGroupMonomorphism_648 -> AgdaAny -> AgdaAny
d_'8315''185''45'homo_670 v0
  = coe
      d_'8315''185''45'homo_632 (coe d_isGroupHomomorphism_656 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupMonomorphism._.homo
d_homo_672 ::
  T_IsGroupMonomorphism_648 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_672 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_isMonoidHomomorphism_630
            (coe d_isGroupHomomorphism_656 (coe v0))))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupMonomorphism._.cong
d_cong_674 ::
  T_IsGroupMonomorphism_648 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_674 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe
               d_isMonoidHomomorphism_630
               (coe d_isGroupHomomorphism_656 (coe v0)))))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupMonomorphism.isMonoidMonomorphism
d_isMonoidMonomorphism_676 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupMonomorphism_648 -> T_IsMonoidMonomorphism_372
d_isMonoidMonomorphism_676 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMonoidMonomorphism_676 v7
du_isMonoidMonomorphism_676 ::
  T_IsGroupMonomorphism_648 -> T_IsMonoidMonomorphism_372
du_isMonoidMonomorphism_676 v0
  = coe
      C_IsMonoidMonomorphism'46'constructor_10237
      (coe
         d_isMonoidHomomorphism_630
         (coe d_isGroupHomomorphism_656 (coe v0)))
      (coe d_injective_658 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupMonomorphism._.isMagmaMonomorphism
d_isMagmaMonomorphism_680 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupMonomorphism_648 -> T_IsMagmaMonomorphism_194
d_isMagmaMonomorphism_680 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_680 v7
du_isMagmaMonomorphism_680 ::
  T_IsGroupMonomorphism_648 -> T_IsMagmaMonomorphism_194
du_isMagmaMonomorphism_680 v0
  = coe
      du_isMagmaMonomorphism_396
      (coe du_isMonoidMonomorphism_676 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupMonomorphism._.isRelMonomorphism
d_isRelMonomorphism_682 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupMonomorphism_648 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_682 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_682 v7
du_isRelMonomorphism_682 ::
  T_IsGroupMonomorphism_648 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_682 v0
  = let v1 = coe du_isMonoidMonomorphism_676 (coe v0) in
    coe
      (coe
         du_isRelMonomorphism_214 (coe du_isMagmaMonomorphism_396 (coe v1)))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupIsomorphism
d_IsGroupIsomorphism_686 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsGroupIsomorphism_686
  = C_IsGroupIsomorphism'46'constructor_17073 T_IsGroupMonomorphism_648
                                              (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupIsomorphism.isGroupMonomorphism
d_isGroupMonomorphism_694 ::
  T_IsGroupIsomorphism_686 -> T_IsGroupMonomorphism_648
d_isGroupMonomorphism_694 v0
  = case coe v0 of
      C_IsGroupIsomorphism'46'constructor_17073 v1 v2 -> coe v1
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupIsomorphism.surjective
d_surjective_696 ::
  T_IsGroupIsomorphism_686 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_696 v0
  = case coe v0 of
      C_IsGroupIsomorphism'46'constructor_17073 v1 v2 -> coe v2
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupIsomorphism._.injective
d_injective_700 ::
  T_IsGroupIsomorphism_686 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_700 v0
  = coe d_injective_658 (coe d_isGroupMonomorphism_694 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupIsomorphism._.isGroupHomomorphism
d_isGroupHomomorphism_702 ::
  T_IsGroupIsomorphism_686 -> T_IsGroupHomomorphism_622
d_isGroupHomomorphism_702 v0
  = coe
      d_isGroupHomomorphism_656 (coe d_isGroupMonomorphism_694 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupIsomorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_704 ::
  T_IsGroupIsomorphism_686 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_704 v0
  = coe
      d_isMagmaHomomorphism_358
      (coe
         d_isMonoidHomomorphism_630
         (coe
            d_isGroupHomomorphism_656
            (coe d_isGroupMonomorphism_694 (coe v0))))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupIsomorphism._.isMagmaMonomorphism
d_isMagmaMonomorphism_706 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupIsomorphism_686 -> T_IsMagmaMonomorphism_194
d_isMagmaMonomorphism_706 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_706 v7
du_isMagmaMonomorphism_706 ::
  T_IsGroupIsomorphism_686 -> T_IsMagmaMonomorphism_194
du_isMagmaMonomorphism_706 v0
  = let v1 = d_isGroupMonomorphism_694 (coe v0) in
    coe
      (coe
         du_isMagmaMonomorphism_396
         (coe du_isMonoidMonomorphism_676 (coe v1)))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupIsomorphism._.isMonoidHomomorphism
d_isMonoidHomomorphism_708 ::
  T_IsGroupIsomorphism_686 -> T_IsMonoidHomomorphism_350
d_isMonoidHomomorphism_708 v0
  = coe
      d_isMonoidHomomorphism_630
      (coe
         d_isGroupHomomorphism_656 (coe d_isGroupMonomorphism_694 (coe v0)))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupIsomorphism._.isMonoidMonomorphism
d_isMonoidMonomorphism_710 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupIsomorphism_686 -> T_IsMonoidMonomorphism_372
d_isMonoidMonomorphism_710 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMonoidMonomorphism_710 v7
du_isMonoidMonomorphism_710 ::
  T_IsGroupIsomorphism_686 -> T_IsMonoidMonomorphism_372
du_isMonoidMonomorphism_710 v0
  = coe
      du_isMonoidMonomorphism_676
      (coe d_isGroupMonomorphism_694 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupIsomorphism._.isRelHomomorphism
d_isRelHomomorphism_712 ::
  T_IsGroupIsomorphism_686 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_712 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_isMonoidHomomorphism_630
            (coe
               d_isGroupHomomorphism_656
               (coe d_isGroupMonomorphism_694 (coe v0)))))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupIsomorphism._.isRelMonomorphism
d_isRelMonomorphism_714 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupIsomorphism_686 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_714 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_714 v7
du_isRelMonomorphism_714 ::
  T_IsGroupIsomorphism_686 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_714 v0
  = let v1 = d_isGroupMonomorphism_694 (coe v0) in
    coe
      (let v2 = coe du_isMonoidMonomorphism_676 (coe v1) in
       coe
         (coe
            du_isRelMonomorphism_214
            (coe du_isMagmaMonomorphism_396 (coe v2))))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupIsomorphism._.ε-homo
d_ε'45'homo_716 :: T_IsGroupIsomorphism_686 -> AgdaAny
d_ε'45'homo_716 v0
  = coe
      d_ε'45'homo_360
      (coe
         d_isMonoidHomomorphism_630
         (coe
            d_isGroupHomomorphism_656
            (coe d_isGroupMonomorphism_694 (coe v0))))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupIsomorphism._.⁻¹-homo
d_'8315''185''45'homo_718 ::
  T_IsGroupIsomorphism_686 -> AgdaAny -> AgdaAny
d_'8315''185''45'homo_718 v0
  = coe
      d_'8315''185''45'homo_632
      (coe
         d_isGroupHomomorphism_656 (coe d_isGroupMonomorphism_694 (coe v0)))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupIsomorphism._.homo
d_homo_720 ::
  T_IsGroupIsomorphism_686 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_720 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_isMonoidHomomorphism_630
            (coe
               d_isGroupHomomorphism_656
               (coe d_isGroupMonomorphism_694 (coe v0)))))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupIsomorphism._.cong
d_cong_722 ::
  T_IsGroupIsomorphism_686 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_722 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe
               d_isMonoidHomomorphism_630
               (coe
                  d_isGroupHomomorphism_656
                  (coe d_isGroupMonomorphism_694 (coe v0))))))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupIsomorphism.isMonoidIsomorphism
d_isMonoidIsomorphism_724 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupIsomorphism_686 -> T_IsMonoidIsomorphism_404
d_isMonoidIsomorphism_724 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMonoidIsomorphism_724 v7
du_isMonoidIsomorphism_724 ::
  T_IsGroupIsomorphism_686 -> T_IsMonoidIsomorphism_404
du_isMonoidIsomorphism_724 v0
  = coe
      C_IsMonoidIsomorphism'46'constructor_11597
      (coe
         du_isMonoidMonomorphism_676
         (coe d_isGroupMonomorphism_694 (coe v0)))
      (coe d_surjective_696 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupIsomorphism._.isMagmaIsomorphism
d_isMagmaIsomorphism_728 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupIsomorphism_686 -> T_IsMagmaIsomorphism_218
d_isMagmaIsomorphism_728 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaIsomorphism_728 v7
du_isMagmaIsomorphism_728 ::
  T_IsGroupIsomorphism_686 -> T_IsMagmaIsomorphism_218
du_isMagmaIsomorphism_728 v0
  = coe
      du_isMagmaIsomorphism_436 (coe du_isMonoidIsomorphism_724 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupIsomorphism._.isRelIsomorphism
d_isRelIsomorphism_730 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupIsomorphism_686 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
d_isRelIsomorphism_730 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelIsomorphism_730 v7
du_isRelIsomorphism_730 ::
  T_IsGroupIsomorphism_686 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
du_isRelIsomorphism_730 v0
  = let v1 = coe du_isMonoidIsomorphism_724 (coe v0) in
    coe
      (coe
         du_isRelIsomorphism_244 (coe du_isMagmaIsomorphism_436 (coe v1)))
-- Algebra.Morphism.Structures.NearSemiringMorphisms._._*_
d__'42'__748 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'42'__748 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du__'42'__748 v4
du__'42'__748 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'42'__748 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__156 (coe v0)
-- Algebra.Morphism.Structures.NearSemiringMorphisms._._≈_
d__'8776'__752 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__752 = erased
-- Algebra.Morphism.Structures.NearSemiringMorphisms._.Carrier
d_Carrier_764 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 -> ()
d_Carrier_764 = erased
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidHomomorphism
d_IsMonoidHomomorphism_788 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidIsomorphism
d_IsMonoidIsomorphism_790 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidMonomorphism
d_IsMonoidMonomorphism_792 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidHomomorphism.homo
d_homo_796 ::
  T_IsMonoidHomomorphism_350 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_796 v0
  = coe d_homo_186 (coe d_isMagmaHomomorphism_358 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidHomomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_798 ::
  T_IsMonoidHomomorphism_350 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_798 v0
  = coe d_isMagmaHomomorphism_358 (coe v0)
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidHomomorphism.isRelHomomorphism
d_isRelHomomorphism_800 ::
  T_IsMonoidHomomorphism_350 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_800 v0
  = coe
      d_isRelHomomorphism_184 (coe d_isMagmaHomomorphism_358 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidHomomorphism.ε-homo
d_ε'45'homo_802 :: T_IsMonoidHomomorphism_350 -> AgdaAny
d_ε'45'homo_802 v0 = coe d_ε'45'homo_360 (coe v0)
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidHomomorphism.cong
d_cong_804 ::
  T_IsMonoidHomomorphism_350 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_804 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184 (coe d_isMagmaHomomorphism_358 (coe v0)))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidIsomorphism.homo
d_homo_808 ::
  T_IsMonoidIsomorphism_404 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_808 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_isMonoidHomomorphism_380
            (coe d_isMonoidMonomorphism_412 (coe v0))))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidIsomorphism.injective
d_injective_810 ::
  T_IsMonoidIsomorphism_404 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_810 v0
  = coe d_injective_382 (coe d_isMonoidMonomorphism_412 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidIsomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_812 ::
  T_IsMonoidIsomorphism_404 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_812 v0
  = coe
      d_isMagmaHomomorphism_358
      (coe
         d_isMonoidHomomorphism_380
         (coe d_isMonoidMonomorphism_412 (coe v0)))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidIsomorphism.isMagmaIsomorphism
d_isMagmaIsomorphism_814 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_404 -> T_IsMagmaIsomorphism_218
d_isMagmaIsomorphism_814 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isMagmaIsomorphism_814
du_isMagmaIsomorphism_814 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_404 -> T_IsMagmaIsomorphism_218
du_isMagmaIsomorphism_814 v0 v1 = coe du_isMagmaIsomorphism_436 v1
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidIsomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_816 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_404 -> T_IsMagmaMonomorphism_194
d_isMagmaMonomorphism_816 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_816 v7
du_isMagmaMonomorphism_816 ::
  T_IsMonoidIsomorphism_404 -> T_IsMagmaMonomorphism_194
du_isMagmaMonomorphism_816 v0
  = coe
      du_isMagmaMonomorphism_396
      (coe d_isMonoidMonomorphism_412 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidIsomorphism.isMonoidHomomorphism
d_isMonoidHomomorphism_818 ::
  T_IsMonoidIsomorphism_404 -> T_IsMonoidHomomorphism_350
d_isMonoidHomomorphism_818 v0
  = coe
      d_isMonoidHomomorphism_380
      (coe d_isMonoidMonomorphism_412 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidIsomorphism.isMonoidMonomorphism
d_isMonoidMonomorphism_820 ::
  T_IsMonoidIsomorphism_404 -> T_IsMonoidMonomorphism_372
d_isMonoidMonomorphism_820 v0
  = coe d_isMonoidMonomorphism_412 (coe v0)
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidIsomorphism.isRelHomomorphism
d_isRelHomomorphism_822 ::
  T_IsMonoidIsomorphism_404 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_822 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_isMonoidHomomorphism_380
            (coe d_isMonoidMonomorphism_412 (coe v0))))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidIsomorphism.isRelIsomorphism
d_isRelIsomorphism_824 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_404 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
d_isRelIsomorphism_824 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelIsomorphism_824 v7
du_isRelIsomorphism_824 ::
  T_IsMonoidIsomorphism_404 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
du_isRelIsomorphism_824 v0
  = coe
      du_isRelIsomorphism_244 (coe du_isMagmaIsomorphism_436 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidIsomorphism.isRelMonomorphism
d_isRelMonomorphism_826 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_404 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_826 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_826 v7
du_isRelMonomorphism_826 ::
  T_IsMonoidIsomorphism_404 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_826 v0
  = let v1 = d_isMonoidMonomorphism_412 (coe v0) in
    coe
      (coe
         du_isRelMonomorphism_214 (coe du_isMagmaMonomorphism_396 (coe v1)))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidIsomorphism.surjective
d_surjective_828 ::
  T_IsMonoidIsomorphism_404 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_828 v0 = coe d_surjective_414 (coe v0)
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidIsomorphism.ε-homo
d_ε'45'homo_830 :: T_IsMonoidIsomorphism_404 -> AgdaAny
d_ε'45'homo_830 v0
  = coe
      d_ε'45'homo_360
      (coe
         d_isMonoidHomomorphism_380
         (coe d_isMonoidMonomorphism_412 (coe v0)))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidIsomorphism.cong
d_cong_832 ::
  T_IsMonoidIsomorphism_404 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_832 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe
               d_isMonoidHomomorphism_380
               (coe d_isMonoidMonomorphism_412 (coe v0)))))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidMonomorphism.homo
d_homo_836 ::
  T_IsMonoidMonomorphism_372 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_836 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe d_isMonoidHomomorphism_380 (coe v0)))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidMonomorphism.injective
d_injective_838 ::
  T_IsMonoidMonomorphism_372 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_838 v0 = coe d_injective_382 (coe v0)
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_840 ::
  T_IsMonoidMonomorphism_372 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_840 v0
  = coe
      d_isMagmaHomomorphism_358 (coe d_isMonoidHomomorphism_380 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidMonomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_842 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidMonomorphism_372 -> T_IsMagmaMonomorphism_194
d_isMagmaMonomorphism_842 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isMagmaMonomorphism_842
du_isMagmaMonomorphism_842 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidMonomorphism_372 -> T_IsMagmaMonomorphism_194
du_isMagmaMonomorphism_842 v0 v1
  = coe du_isMagmaMonomorphism_396 v1
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidMonomorphism.isMonoidHomomorphism
d_isMonoidHomomorphism_844 ::
  T_IsMonoidMonomorphism_372 -> T_IsMonoidHomomorphism_350
d_isMonoidHomomorphism_844 v0
  = coe d_isMonoidHomomorphism_380 (coe v0)
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidMonomorphism.isRelHomomorphism
d_isRelHomomorphism_846 ::
  T_IsMonoidMonomorphism_372 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_846 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe d_isMonoidHomomorphism_380 (coe v0)))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidMonomorphism.isRelMonomorphism
d_isRelMonomorphism_848 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidMonomorphism_372 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_848 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_848 v7
du_isRelMonomorphism_848 ::
  T_IsMonoidMonomorphism_372 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_848 v0
  = coe
      du_isRelMonomorphism_214 (coe du_isMagmaMonomorphism_396 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidMonomorphism.ε-homo
d_ε'45'homo_850 :: T_IsMonoidMonomorphism_372 -> AgdaAny
d_ε'45'homo_850 v0
  = coe d_ε'45'homo_360 (coe d_isMonoidHomomorphism_380 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidMonomorphism.cong
d_cong_852 ::
  T_IsMonoidMonomorphism_372 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_852 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe d_isMonoidHomomorphism_380 (coe v0))))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaHomomorphism
d_IsMagmaHomomorphism_856 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaIsomorphism
d_IsMagmaIsomorphism_858 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaMonomorphism
d_IsMagmaMonomorphism_860 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaHomomorphism.homo
d_homo_864 ::
  T_IsMagmaHomomorphism_176 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_864 v0 = coe d_homo_186 (coe v0)
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaHomomorphism.isRelHomomorphism
d_isRelHomomorphism_866 ::
  T_IsMagmaHomomorphism_176 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_866 v0 = coe d_isRelHomomorphism_184 (coe v0)
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaHomomorphism.cong
d_cong_868 ::
  T_IsMagmaHomomorphism_176 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_868 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe d_isRelHomomorphism_184 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaIsomorphism.homo
d_homo_872 ::
  T_IsMagmaIsomorphism_218 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_872 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_202 (coe d_isMagmaMonomorphism_226 (coe v0)))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaIsomorphism.injective
d_injective_874 ::
  T_IsMagmaIsomorphism_218 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_874 v0
  = coe d_injective_204 (coe d_isMagmaMonomorphism_226 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaIsomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_876 ::
  T_IsMagmaIsomorphism_218 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_876 v0
  = coe
      d_isMagmaHomomorphism_202 (coe d_isMagmaMonomorphism_226 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaIsomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_878 ::
  T_IsMagmaIsomorphism_218 -> T_IsMagmaMonomorphism_194
d_isMagmaMonomorphism_878 v0
  = coe d_isMagmaMonomorphism_226 (coe v0)
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaIsomorphism.isRelHomomorphism
d_isRelHomomorphism_880 ::
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_880 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_202 (coe d_isMagmaMonomorphism_226 (coe v0)))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaIsomorphism.isRelIsomorphism
d_isRelIsomorphism_882 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
d_isRelIsomorphism_882 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isRelIsomorphism_882
du_isRelIsomorphism_882 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
du_isRelIsomorphism_882 v0 v1 = coe du_isRelIsomorphism_244 v1
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaIsomorphism.isRelMonomorphism
d_isRelMonomorphism_884 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_884 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_884 v7
du_isRelMonomorphism_884 ::
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_884 v0
  = coe
      du_isRelMonomorphism_214 (coe d_isMagmaMonomorphism_226 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaIsomorphism.surjective
d_surjective_886 ::
  T_IsMagmaIsomorphism_218 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_886 v0 = coe d_surjective_228 (coe v0)
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaIsomorphism.cong
d_cong_888 ::
  T_IsMagmaIsomorphism_218 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_888 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_202
            (coe d_isMagmaMonomorphism_226 (coe v0))))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaMonomorphism.homo
d_homo_892 ::
  T_IsMagmaMonomorphism_194 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_892 v0
  = coe d_homo_186 (coe d_isMagmaHomomorphism_202 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaMonomorphism.injective
d_injective_894 ::
  T_IsMagmaMonomorphism_194 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_894 v0 = coe d_injective_204 (coe v0)
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_896 ::
  T_IsMagmaMonomorphism_194 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_896 v0
  = coe d_isMagmaHomomorphism_202 (coe v0)
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaMonomorphism.isRelHomomorphism
d_isRelHomomorphism_898 ::
  T_IsMagmaMonomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_898 v0
  = coe
      d_isRelHomomorphism_184 (coe d_isMagmaHomomorphism_202 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaMonomorphism.isRelMonomorphism
d_isRelMonomorphism_900 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_900 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isRelMonomorphism_900
du_isRelMonomorphism_900 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_900 v0 v1 = coe du_isRelMonomorphism_214 v1
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaMonomorphism.cong
d_cong_902 ::
  T_IsMagmaMonomorphism_194 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_902 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184 (coe d_isMagmaHomomorphism_202 (coe v0)))
-- Algebra.Morphism.Structures.NearSemiringMorphisms._.Homomorphic₂
d_Homomorphic'8322'_910 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8322'_910 = erased
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringHomomorphism
d_IsNearSemiringHomomorphism_916 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsNearSemiringHomomorphism_916
  = C_IsNearSemiringHomomorphism'46'constructor_19989 T_IsMonoidHomomorphism_350
                                                      (AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringHomomorphism.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_924 ::
  T_IsNearSemiringHomomorphism_916 -> T_IsMonoidHomomorphism_350
d_'43''45'isMonoidHomomorphism_924 v0
  = case coe v0 of
      C_IsNearSemiringHomomorphism'46'constructor_19989 v1 v2 -> coe v1
      _                                                       -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringHomomorphism.*-homo
d_'42''45'homo_926 ::
  T_IsNearSemiringHomomorphism_916 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_926 v0
  = case coe v0 of
      C_IsNearSemiringHomomorphism'46'constructor_19989 v1 v2 -> coe v2
      _                                                       -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringHomomorphism._.homo
d_homo_930 ::
  T_IsNearSemiringHomomorphism_916 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_930 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe d_'43''45'isMonoidHomomorphism_924 (coe v0)))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringHomomorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_932 ::
  T_IsNearSemiringHomomorphism_916 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_932 v0
  = coe
      d_isMagmaHomomorphism_358
      (coe d_'43''45'isMonoidHomomorphism_924 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringHomomorphism._.ε-homo
d_ε'45'homo_934 :: T_IsNearSemiringHomomorphism_916 -> AgdaAny
d_ε'45'homo_934 v0
  = coe
      d_ε'45'homo_360 (coe d_'43''45'isMonoidHomomorphism_924 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringHomomorphism._.isRelHomomorphism
d_isRelHomomorphism_936 ::
  T_IsNearSemiringHomomorphism_916 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_936 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe d_'43''45'isMonoidHomomorphism_924 (coe v0)))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringHomomorphism._.cong
d_cong_938 ::
  T_IsNearSemiringHomomorphism_916 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_938 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe d_'43''45'isMonoidHomomorphism_924 (coe v0))))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringHomomorphism.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_940 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringHomomorphism_916 -> T_IsMagmaHomomorphism_176
d_'42''45'isMagmaHomomorphism_940 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_940 v7
du_'42''45'isMagmaHomomorphism_940 ::
  T_IsNearSemiringHomomorphism_916 -> T_IsMagmaHomomorphism_176
du_'42''45'isMagmaHomomorphism_940 v0
  = coe
      C_IsMagmaHomomorphism'46'constructor_4629
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe d_'43''45'isMonoidHomomorphism_924 (coe v0))))
      (coe d_'42''45'homo_926 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringMonomorphism
d_IsNearSemiringMonomorphism_944 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsNearSemiringMonomorphism_944
  = C_IsNearSemiringMonomorphism'46'constructor_21119 T_IsNearSemiringHomomorphism_916
                                                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringMonomorphism.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_952 ::
  T_IsNearSemiringMonomorphism_944 ->
  T_IsNearSemiringHomomorphism_916
d_isNearSemiringHomomorphism_952 v0
  = case coe v0 of
      C_IsNearSemiringMonomorphism'46'constructor_21119 v1 v2 -> coe v1
      _                                                       -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringMonomorphism.injective
d_injective_954 ::
  T_IsNearSemiringMonomorphism_944 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_954 v0
  = case coe v0 of
      C_IsNearSemiringMonomorphism'46'constructor_21119 v1 v2 -> coe v2
      _                                                       -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringMonomorphism._.*-homo
d_'42''45'homo_958 ::
  T_IsNearSemiringMonomorphism_944 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_958 v0
  = coe
      d_'42''45'homo_926 (coe d_isNearSemiringHomomorphism_952 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringMonomorphism._.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_960 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringMonomorphism_944 -> T_IsMagmaHomomorphism_176
d_'42''45'isMagmaHomomorphism_960 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_960 v7
du_'42''45'isMagmaHomomorphism_960 ::
  T_IsNearSemiringMonomorphism_944 -> T_IsMagmaHomomorphism_176
du_'42''45'isMagmaHomomorphism_960 v0
  = coe
      du_'42''45'isMagmaHomomorphism_940
      (coe d_isNearSemiringHomomorphism_952 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringMonomorphism._.homo
d_homo_962 ::
  T_IsNearSemiringMonomorphism_944 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_962 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_'43''45'isMonoidHomomorphism_924
            (coe d_isNearSemiringHomomorphism_952 (coe v0))))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringMonomorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_964 ::
  T_IsNearSemiringMonomorphism_944 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_964 v0
  = coe
      d_isMagmaHomomorphism_358
      (coe
         d_'43''45'isMonoidHomomorphism_924
         (coe d_isNearSemiringHomomorphism_952 (coe v0)))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringMonomorphism._.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_966 ::
  T_IsNearSemiringMonomorphism_944 -> T_IsMonoidHomomorphism_350
d_'43''45'isMonoidHomomorphism_966 v0
  = coe
      d_'43''45'isMonoidHomomorphism_924
      (coe d_isNearSemiringHomomorphism_952 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringMonomorphism._.ε-homo
d_ε'45'homo_968 :: T_IsNearSemiringMonomorphism_944 -> AgdaAny
d_ε'45'homo_968 v0
  = coe
      d_ε'45'homo_360
      (coe
         d_'43''45'isMonoidHomomorphism_924
         (coe d_isNearSemiringHomomorphism_952 (coe v0)))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringMonomorphism._.isRelHomomorphism
d_isRelHomomorphism_970 ::
  T_IsNearSemiringMonomorphism_944 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_970 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_'43''45'isMonoidHomomorphism_924
            (coe d_isNearSemiringHomomorphism_952 (coe v0))))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringMonomorphism._.cong
d_cong_972 ::
  T_IsNearSemiringMonomorphism_944 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_972 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe
               d_'43''45'isMonoidHomomorphism_924
               (coe d_isNearSemiringHomomorphism_952 (coe v0)))))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringMonomorphism.+-isMonoidMonomorphism
d_'43''45'isMonoidMonomorphism_974 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringMonomorphism_944 -> T_IsMonoidMonomorphism_372
d_'43''45'isMonoidMonomorphism_974 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isMonoidMonomorphism_974 v7
du_'43''45'isMonoidMonomorphism_974 ::
  T_IsNearSemiringMonomorphism_944 -> T_IsMonoidMonomorphism_372
du_'43''45'isMonoidMonomorphism_974 v0
  = coe
      C_IsMonoidMonomorphism'46'constructor_10237
      (coe
         d_'43''45'isMonoidHomomorphism_924
         (coe d_isNearSemiringHomomorphism_952 (coe v0)))
      (coe d_injective_954 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringMonomorphism._.isMagmaMonomorphism
d_isMagmaMonomorphism_978 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringMonomorphism_944 -> T_IsMagmaMonomorphism_194
d_isMagmaMonomorphism_978 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_978 v7
du_isMagmaMonomorphism_978 ::
  T_IsNearSemiringMonomorphism_944 -> T_IsMagmaMonomorphism_194
du_isMagmaMonomorphism_978 v0
  = coe
      du_isMagmaMonomorphism_396
      (coe du_'43''45'isMonoidMonomorphism_974 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringMonomorphism._.isRelMonomorphism
d_isRelMonomorphism_980 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringMonomorphism_944 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_980 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_980 v7
du_isRelMonomorphism_980 ::
  T_IsNearSemiringMonomorphism_944 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_980 v0
  = let v1 = coe du_'43''45'isMonoidMonomorphism_974 (coe v0) in
    coe
      (coe
         du_isRelMonomorphism_214 (coe du_isMagmaMonomorphism_396 (coe v1)))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringMonomorphism.*-isMagmaMonomorphism
d_'42''45'isMagmaMonomorphism_982 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringMonomorphism_944 -> T_IsMagmaMonomorphism_194
d_'42''45'isMagmaMonomorphism_982 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaMonomorphism_982 v7
du_'42''45'isMagmaMonomorphism_982 ::
  T_IsNearSemiringMonomorphism_944 -> T_IsMagmaMonomorphism_194
du_'42''45'isMagmaMonomorphism_982 v0
  = coe
      C_IsMagmaMonomorphism'46'constructor_5763
      (coe
         du_'42''45'isMagmaHomomorphism_940
         (coe d_isNearSemiringHomomorphism_952 (coe v0)))
      (coe d_injective_954 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism
d_IsNearSemiringIsomorphism_986 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsNearSemiringIsomorphism_986
  = C_IsNearSemiringIsomorphism'46'constructor_23007 T_IsNearSemiringMonomorphism_944
                                                     (AgdaAny ->
                                                      MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism.isNearSemiringMonomorphism
d_isNearSemiringMonomorphism_994 ::
  T_IsNearSemiringIsomorphism_986 -> T_IsNearSemiringMonomorphism_944
d_isNearSemiringMonomorphism_994 v0
  = case coe v0 of
      C_IsNearSemiringIsomorphism'46'constructor_23007 v1 v2 -> coe v1
      _                                                      -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism.surjective
d_surjective_996 ::
  T_IsNearSemiringIsomorphism_986 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_996 v0
  = case coe v0 of
      C_IsNearSemiringIsomorphism'46'constructor_23007 v1 v2 -> coe v2
      _                                                      -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism._.*-homo
d_'42''45'homo_1000 ::
  T_IsNearSemiringIsomorphism_986 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_1000 v0
  = coe
      d_'42''45'homo_926
      (coe
         d_isNearSemiringHomomorphism_952
         (coe d_isNearSemiringMonomorphism_994 (coe v0)))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism._.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_1002 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_986 -> T_IsMagmaHomomorphism_176
d_'42''45'isMagmaHomomorphism_1002 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_1002 v7
du_'42''45'isMagmaHomomorphism_1002 ::
  T_IsNearSemiringIsomorphism_986 -> T_IsMagmaHomomorphism_176
du_'42''45'isMagmaHomomorphism_1002 v0
  = let v1 = d_isNearSemiringMonomorphism_994 (coe v0) in
    coe
      (coe
         du_'42''45'isMagmaHomomorphism_940
         (coe d_isNearSemiringHomomorphism_952 (coe v1)))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism._.*-isMagmaMonomorphism
d_'42''45'isMagmaMonomorphism_1004 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_986 -> T_IsMagmaMonomorphism_194
d_'42''45'isMagmaMonomorphism_1004 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaMonomorphism_1004 v7
du_'42''45'isMagmaMonomorphism_1004 ::
  T_IsNearSemiringIsomorphism_986 -> T_IsMagmaMonomorphism_194
du_'42''45'isMagmaMonomorphism_1004 v0
  = coe
      du_'42''45'isMagmaMonomorphism_982
      (coe d_isNearSemiringMonomorphism_994 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism._.homo
d_homo_1006 ::
  T_IsNearSemiringIsomorphism_986 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1006 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_'43''45'isMonoidHomomorphism_924
            (coe
               d_isNearSemiringHomomorphism_952
               (coe d_isNearSemiringMonomorphism_994 (coe v0)))))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_1008 ::
  T_IsNearSemiringIsomorphism_986 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_1008 v0
  = coe
      d_isMagmaHomomorphism_358
      (coe
         d_'43''45'isMonoidHomomorphism_924
         (coe
            d_isNearSemiringHomomorphism_952
            (coe d_isNearSemiringMonomorphism_994 (coe v0))))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism._.isMagmaMonomorphism
d_isMagmaMonomorphism_1010 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_986 -> T_IsMagmaMonomorphism_194
d_isMagmaMonomorphism_1010 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_1010 v7
du_isMagmaMonomorphism_1010 ::
  T_IsNearSemiringIsomorphism_986 -> T_IsMagmaMonomorphism_194
du_isMagmaMonomorphism_1010 v0
  = let v1 = d_isNearSemiringMonomorphism_994 (coe v0) in
    coe
      (coe
         du_isMagmaMonomorphism_396
         (coe du_'43''45'isMonoidMonomorphism_974 (coe v1)))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism._.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_1012 ::
  T_IsNearSemiringIsomorphism_986 -> T_IsMonoidHomomorphism_350
d_'43''45'isMonoidHomomorphism_1012 v0
  = coe
      d_'43''45'isMonoidHomomorphism_924
      (coe
         d_isNearSemiringHomomorphism_952
         (coe d_isNearSemiringMonomorphism_994 (coe v0)))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism._.+-isMonoidMonomorphism
d_'43''45'isMonoidMonomorphism_1014 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_986 -> T_IsMonoidMonomorphism_372
d_'43''45'isMonoidMonomorphism_1014 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isMonoidMonomorphism_1014 v7
du_'43''45'isMonoidMonomorphism_1014 ::
  T_IsNearSemiringIsomorphism_986 -> T_IsMonoidMonomorphism_372
du_'43''45'isMonoidMonomorphism_1014 v0
  = coe
      du_'43''45'isMonoidMonomorphism_974
      (coe d_isNearSemiringMonomorphism_994 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism._.ε-homo
d_ε'45'homo_1016 :: T_IsNearSemiringIsomorphism_986 -> AgdaAny
d_ε'45'homo_1016 v0
  = coe
      d_ε'45'homo_360
      (coe
         d_'43''45'isMonoidHomomorphism_924
         (coe
            d_isNearSemiringHomomorphism_952
            (coe d_isNearSemiringMonomorphism_994 (coe v0))))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism._.injective
d_injective_1018 ::
  T_IsNearSemiringIsomorphism_986 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_1018 v0
  = coe
      d_injective_954 (coe d_isNearSemiringMonomorphism_994 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism._.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_1020 ::
  T_IsNearSemiringIsomorphism_986 -> T_IsNearSemiringHomomorphism_916
d_isNearSemiringHomomorphism_1020 v0
  = coe
      d_isNearSemiringHomomorphism_952
      (coe d_isNearSemiringMonomorphism_994 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism._.isRelHomomorphism
d_isRelHomomorphism_1022 ::
  T_IsNearSemiringIsomorphism_986 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1022 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_'43''45'isMonoidHomomorphism_924
            (coe
               d_isNearSemiringHomomorphism_952
               (coe d_isNearSemiringMonomorphism_994 (coe v0)))))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism._.isRelMonomorphism
d_isRelMonomorphism_1024 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_986 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_1024 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_1024 v7
du_isRelMonomorphism_1024 ::
  T_IsNearSemiringIsomorphism_986 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_1024 v0
  = let v1 = d_isNearSemiringMonomorphism_994 (coe v0) in
    coe
      (let v2 = coe du_'43''45'isMonoidMonomorphism_974 (coe v1) in
       coe
         (coe
            du_isRelMonomorphism_214
            (coe du_isMagmaMonomorphism_396 (coe v2))))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism._.cong
d_cong_1026 ::
  T_IsNearSemiringIsomorphism_986 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1026 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe
               d_'43''45'isMonoidHomomorphism_924
               (coe
                  d_isNearSemiringHomomorphism_952
                  (coe d_isNearSemiringMonomorphism_994 (coe v0))))))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism.+-isMonoidIsomorphism
d_'43''45'isMonoidIsomorphism_1028 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_986 -> T_IsMonoidIsomorphism_404
d_'43''45'isMonoidIsomorphism_1028 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isMonoidIsomorphism_1028 v7
du_'43''45'isMonoidIsomorphism_1028 ::
  T_IsNearSemiringIsomorphism_986 -> T_IsMonoidIsomorphism_404
du_'43''45'isMonoidIsomorphism_1028 v0
  = coe
      C_IsMonoidIsomorphism'46'constructor_11597
      (coe
         du_'43''45'isMonoidMonomorphism_974
         (coe d_isNearSemiringMonomorphism_994 (coe v0)))
      (coe d_surjective_996 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism._.isMagmaIsomorphism
d_isMagmaIsomorphism_1032 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_986 -> T_IsMagmaIsomorphism_218
d_isMagmaIsomorphism_1032 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaIsomorphism_1032 v7
du_isMagmaIsomorphism_1032 ::
  T_IsNearSemiringIsomorphism_986 -> T_IsMagmaIsomorphism_218
du_isMagmaIsomorphism_1032 v0
  = coe
      du_isMagmaIsomorphism_436
      (coe du_'43''45'isMonoidIsomorphism_1028 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism._.isRelIsomorphism
d_isRelIsomorphism_1034 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_986 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
d_isRelIsomorphism_1034 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelIsomorphism_1034 v7
du_isRelIsomorphism_1034 ::
  T_IsNearSemiringIsomorphism_986 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
du_isRelIsomorphism_1034 v0
  = let v1 = coe du_'43''45'isMonoidIsomorphism_1028 (coe v0) in
    coe
      (coe
         du_isRelIsomorphism_244 (coe du_isMagmaIsomorphism_436 (coe v1)))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism.*-isMagmaIsomorphism
d_'42''45'isMagmaIsomorphism_1036 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_986 -> T_IsMagmaIsomorphism_218
d_'42''45'isMagmaIsomorphism_1036 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaIsomorphism_1036 v7
du_'42''45'isMagmaIsomorphism_1036 ::
  T_IsNearSemiringIsomorphism_986 -> T_IsMagmaIsomorphism_218
du_'42''45'isMagmaIsomorphism_1036 v0
  = coe
      C_IsMagmaIsomorphism'46'constructor_7199
      (coe
         du_'42''45'isMagmaMonomorphism_982
         (coe d_isNearSemiringMonomorphism_994 (coe v0)))
      (coe d_surjective_996 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms._._≈_
d__'8776'__1058 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__1058 = erased
-- Algebra.Morphism.Structures.SemiringMorphisms._.1#
d_1'35'_1072 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 -> AgdaAny
d_1'35'_1072 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_1'35'_1072 v4
du_1'35'_1072 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 -> AgdaAny
du_1'35'_1072 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d_1'35'_202 (coe v0)
-- Algebra.Morphism.Structures.SemiringMorphisms._.Carrier
d_Carrier_1074 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 -> ()
d_Carrier_1074 = erased
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidHomomorphism
d_IsMonoidHomomorphism_1106 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidIsomorphism
d_IsMonoidIsomorphism_1108 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidMonomorphism
d_IsMonoidMonomorphism_1110 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidHomomorphism.homo
d_homo_1114 ::
  T_IsMonoidHomomorphism_350 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1114 v0
  = coe d_homo_186 (coe d_isMagmaHomomorphism_358 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidHomomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_1116 ::
  T_IsMonoidHomomorphism_350 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_1116 v0
  = coe d_isMagmaHomomorphism_358 (coe v0)
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidHomomorphism.isRelHomomorphism
d_isRelHomomorphism_1118 ::
  T_IsMonoidHomomorphism_350 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1118 v0
  = coe
      d_isRelHomomorphism_184 (coe d_isMagmaHomomorphism_358 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidHomomorphism.ε-homo
d_ε'45'homo_1120 :: T_IsMonoidHomomorphism_350 -> AgdaAny
d_ε'45'homo_1120 v0 = coe d_ε'45'homo_360 (coe v0)
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidHomomorphism.cong
d_cong_1122 ::
  T_IsMonoidHomomorphism_350 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1122 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184 (coe d_isMagmaHomomorphism_358 (coe v0)))
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidIsomorphism.homo
d_homo_1126 ::
  T_IsMonoidIsomorphism_404 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1126 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_isMonoidHomomorphism_380
            (coe d_isMonoidMonomorphism_412 (coe v0))))
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidIsomorphism.injective
d_injective_1128 ::
  T_IsMonoidIsomorphism_404 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_1128 v0
  = coe d_injective_382 (coe d_isMonoidMonomorphism_412 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidIsomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_1130 ::
  T_IsMonoidIsomorphism_404 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_1130 v0
  = coe
      d_isMagmaHomomorphism_358
      (coe
         d_isMonoidHomomorphism_380
         (coe d_isMonoidMonomorphism_412 (coe v0)))
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidIsomorphism.isMagmaIsomorphism
d_isMagmaIsomorphism_1132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_404 -> T_IsMagmaIsomorphism_218
d_isMagmaIsomorphism_1132 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isMagmaIsomorphism_1132
du_isMagmaIsomorphism_1132 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_404 -> T_IsMagmaIsomorphism_218
du_isMagmaIsomorphism_1132 v0 v1 = coe du_isMagmaIsomorphism_436 v1
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidIsomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_1134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_404 -> T_IsMagmaMonomorphism_194
d_isMagmaMonomorphism_1134 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_1134 v7
du_isMagmaMonomorphism_1134 ::
  T_IsMonoidIsomorphism_404 -> T_IsMagmaMonomorphism_194
du_isMagmaMonomorphism_1134 v0
  = coe
      du_isMagmaMonomorphism_396
      (coe d_isMonoidMonomorphism_412 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidIsomorphism.isMonoidHomomorphism
d_isMonoidHomomorphism_1136 ::
  T_IsMonoidIsomorphism_404 -> T_IsMonoidHomomorphism_350
d_isMonoidHomomorphism_1136 v0
  = coe
      d_isMonoidHomomorphism_380
      (coe d_isMonoidMonomorphism_412 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidIsomorphism.isMonoidMonomorphism
d_isMonoidMonomorphism_1138 ::
  T_IsMonoidIsomorphism_404 -> T_IsMonoidMonomorphism_372
d_isMonoidMonomorphism_1138 v0
  = coe d_isMonoidMonomorphism_412 (coe v0)
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidIsomorphism.isRelHomomorphism
d_isRelHomomorphism_1140 ::
  T_IsMonoidIsomorphism_404 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1140 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_isMonoidHomomorphism_380
            (coe d_isMonoidMonomorphism_412 (coe v0))))
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidIsomorphism.isRelIsomorphism
d_isRelIsomorphism_1142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_404 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
d_isRelIsomorphism_1142 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelIsomorphism_1142 v7
du_isRelIsomorphism_1142 ::
  T_IsMonoidIsomorphism_404 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
du_isRelIsomorphism_1142 v0
  = coe
      du_isRelIsomorphism_244 (coe du_isMagmaIsomorphism_436 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidIsomorphism.isRelMonomorphism
d_isRelMonomorphism_1144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_404 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_1144 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_1144 v7
du_isRelMonomorphism_1144 ::
  T_IsMonoidIsomorphism_404 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_1144 v0
  = let v1 = d_isMonoidMonomorphism_412 (coe v0) in
    coe
      (coe
         du_isRelMonomorphism_214 (coe du_isMagmaMonomorphism_396 (coe v1)))
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidIsomorphism.surjective
d_surjective_1146 ::
  T_IsMonoidIsomorphism_404 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_1146 v0 = coe d_surjective_414 (coe v0)
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidIsomorphism.ε-homo
d_ε'45'homo_1148 :: T_IsMonoidIsomorphism_404 -> AgdaAny
d_ε'45'homo_1148 v0
  = coe
      d_ε'45'homo_360
      (coe
         d_isMonoidHomomorphism_380
         (coe d_isMonoidMonomorphism_412 (coe v0)))
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidIsomorphism.cong
d_cong_1150 ::
  T_IsMonoidIsomorphism_404 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1150 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe
               d_isMonoidHomomorphism_380
               (coe d_isMonoidMonomorphism_412 (coe v0)))))
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidMonomorphism.homo
d_homo_1154 ::
  T_IsMonoidMonomorphism_372 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1154 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe d_isMonoidHomomorphism_380 (coe v0)))
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidMonomorphism.injective
d_injective_1156 ::
  T_IsMonoidMonomorphism_372 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_1156 v0 = coe d_injective_382 (coe v0)
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_1158 ::
  T_IsMonoidMonomorphism_372 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_1158 v0
  = coe
      d_isMagmaHomomorphism_358 (coe d_isMonoidHomomorphism_380 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidMonomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_1160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidMonomorphism_372 -> T_IsMagmaMonomorphism_194
d_isMagmaMonomorphism_1160 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isMagmaMonomorphism_1160
du_isMagmaMonomorphism_1160 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidMonomorphism_372 -> T_IsMagmaMonomorphism_194
du_isMagmaMonomorphism_1160 v0 v1
  = coe du_isMagmaMonomorphism_396 v1
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidMonomorphism.isMonoidHomomorphism
d_isMonoidHomomorphism_1162 ::
  T_IsMonoidMonomorphism_372 -> T_IsMonoidHomomorphism_350
d_isMonoidHomomorphism_1162 v0
  = coe d_isMonoidHomomorphism_380 (coe v0)
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidMonomorphism.isRelHomomorphism
d_isRelHomomorphism_1164 ::
  T_IsMonoidMonomorphism_372 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1164 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe d_isMonoidHomomorphism_380 (coe v0)))
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidMonomorphism.isRelMonomorphism
d_isRelMonomorphism_1166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidMonomorphism_372 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_1166 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_1166 v7
du_isRelMonomorphism_1166 ::
  T_IsMonoidMonomorphism_372 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_1166 v0
  = coe
      du_isRelMonomorphism_214 (coe du_isMagmaMonomorphism_396 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidMonomorphism.ε-homo
d_ε'45'homo_1168 :: T_IsMonoidMonomorphism_372 -> AgdaAny
d_ε'45'homo_1168 v0
  = coe d_ε'45'homo_360 (coe d_isMonoidHomomorphism_380 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidMonomorphism.cong
d_cong_1170 ::
  T_IsMonoidMonomorphism_372 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1170 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe d_isMonoidHomomorphism_380 (coe v0))))
-- Algebra.Morphism.Structures.SemiringMorphisms._.Homomorphic₀
d_Homomorphic'8320'_1174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> ()
d_Homomorphic'8320'_1174 = erased
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringHomomorphism
d_IsNearSemiringHomomorphism_1184 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism
d_IsNearSemiringIsomorphism_1186 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringMonomorphism
d_IsNearSemiringMonomorphism_1188 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringHomomorphism.*-homo
d_'42''45'homo_1192 ::
  T_IsNearSemiringHomomorphism_916 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_1192 v0 = coe d_'42''45'homo_926 (coe v0)
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringHomomorphism.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_1194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringHomomorphism_916 -> T_IsMagmaHomomorphism_176
d_'42''45'isMagmaHomomorphism_1194 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'42''45'isMagmaHomomorphism_1194
du_'42''45'isMagmaHomomorphism_1194 ::
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringHomomorphism_916 -> T_IsMagmaHomomorphism_176
du_'42''45'isMagmaHomomorphism_1194 v0 v1
  = coe du_'42''45'isMagmaHomomorphism_940 v1
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringHomomorphism.homo
d_homo_1196 ::
  T_IsNearSemiringHomomorphism_916 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1196 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe d_'43''45'isMonoidHomomorphism_924 (coe v0)))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringHomomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_1198 ::
  T_IsNearSemiringHomomorphism_916 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_1198 v0
  = coe
      d_isMagmaHomomorphism_358
      (coe d_'43''45'isMonoidHomomorphism_924 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringHomomorphism.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_1200 ::
  T_IsNearSemiringHomomorphism_916 -> T_IsMonoidHomomorphism_350
d_'43''45'isMonoidHomomorphism_1200 v0
  = coe d_'43''45'isMonoidHomomorphism_924 (coe v0)
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringHomomorphism.ε-homo
d_ε'45'homo_1202 :: T_IsNearSemiringHomomorphism_916 -> AgdaAny
d_ε'45'homo_1202 v0
  = coe
      d_ε'45'homo_360 (coe d_'43''45'isMonoidHomomorphism_924 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringHomomorphism.isRelHomomorphism
d_isRelHomomorphism_1204 ::
  T_IsNearSemiringHomomorphism_916 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1204 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe d_'43''45'isMonoidHomomorphism_924 (coe v0)))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringHomomorphism.cong
d_cong_1206 ::
  T_IsNearSemiringHomomorphism_916 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1206 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe d_'43''45'isMonoidHomomorphism_924 (coe v0))))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism.*-homo
d_'42''45'homo_1210 ::
  T_IsNearSemiringIsomorphism_986 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_1210 v0
  = coe
      d_'42''45'homo_926
      (coe
         d_isNearSemiringHomomorphism_952
         (coe d_isNearSemiringMonomorphism_994 (coe v0)))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_1212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_986 -> T_IsMagmaHomomorphism_176
d_'42''45'isMagmaHomomorphism_1212 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_1212 v7
du_'42''45'isMagmaHomomorphism_1212 ::
  T_IsNearSemiringIsomorphism_986 -> T_IsMagmaHomomorphism_176
du_'42''45'isMagmaHomomorphism_1212 v0
  = let v1 = d_isNearSemiringMonomorphism_994 (coe v0) in
    coe
      (coe
         du_'42''45'isMagmaHomomorphism_940
         (coe d_isNearSemiringHomomorphism_952 (coe v1)))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism.*-isMagmaIsomorphism
d_'42''45'isMagmaIsomorphism_1214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_986 -> T_IsMagmaIsomorphism_218
d_'42''45'isMagmaIsomorphism_1214 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'42''45'isMagmaIsomorphism_1214
du_'42''45'isMagmaIsomorphism_1214 ::
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_986 -> T_IsMagmaIsomorphism_218
du_'42''45'isMagmaIsomorphism_1214 v0 v1
  = coe du_'42''45'isMagmaIsomorphism_1036 v1
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism.*-isMagmaMonomorphism
d_'42''45'isMagmaMonomorphism_1216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_986 -> T_IsMagmaMonomorphism_194
d_'42''45'isMagmaMonomorphism_1216 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaMonomorphism_1216 v7
du_'42''45'isMagmaMonomorphism_1216 ::
  T_IsNearSemiringIsomorphism_986 -> T_IsMagmaMonomorphism_194
du_'42''45'isMagmaMonomorphism_1216 v0
  = coe
      du_'42''45'isMagmaMonomorphism_982
      (coe d_isNearSemiringMonomorphism_994 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism.homo
d_homo_1218 ::
  T_IsNearSemiringIsomorphism_986 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1218 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_'43''45'isMonoidHomomorphism_924
            (coe
               d_isNearSemiringHomomorphism_952
               (coe d_isNearSemiringMonomorphism_994 (coe v0)))))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_1220 ::
  T_IsNearSemiringIsomorphism_986 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_1220 v0
  = coe
      d_isMagmaHomomorphism_358
      (coe
         d_'43''45'isMonoidHomomorphism_924
         (coe
            d_isNearSemiringHomomorphism_952
            (coe d_isNearSemiringMonomorphism_994 (coe v0))))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism.isMagmaIsomorphism
d_isMagmaIsomorphism_1222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_986 -> T_IsMagmaIsomorphism_218
d_isMagmaIsomorphism_1222 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaIsomorphism_1222 v7
du_isMagmaIsomorphism_1222 ::
  T_IsNearSemiringIsomorphism_986 -> T_IsMagmaIsomorphism_218
du_isMagmaIsomorphism_1222 v0
  = coe
      du_isMagmaIsomorphism_436
      (coe du_'43''45'isMonoidIsomorphism_1028 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_1224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_986 -> T_IsMagmaMonomorphism_194
d_isMagmaMonomorphism_1224 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_1224 v7
du_isMagmaMonomorphism_1224 ::
  T_IsNearSemiringIsomorphism_986 -> T_IsMagmaMonomorphism_194
du_isMagmaMonomorphism_1224 v0
  = let v1 = d_isNearSemiringMonomorphism_994 (coe v0) in
    coe
      (coe
         du_isMagmaMonomorphism_396
         (coe du_'43''45'isMonoidMonomorphism_974 (coe v1)))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_1226 ::
  T_IsNearSemiringIsomorphism_986 -> T_IsMonoidHomomorphism_350
d_'43''45'isMonoidHomomorphism_1226 v0
  = coe
      d_'43''45'isMonoidHomomorphism_924
      (coe
         d_isNearSemiringHomomorphism_952
         (coe d_isNearSemiringMonomorphism_994 (coe v0)))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism.+-isMonoidIsomorphism
d_'43''45'isMonoidIsomorphism_1228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_986 -> T_IsMonoidIsomorphism_404
d_'43''45'isMonoidIsomorphism_1228 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'43''45'isMonoidIsomorphism_1228
du_'43''45'isMonoidIsomorphism_1228 ::
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_986 -> T_IsMonoidIsomorphism_404
du_'43''45'isMonoidIsomorphism_1228 v0 v1
  = coe du_'43''45'isMonoidIsomorphism_1028 v1
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism.+-isMonoidMonomorphism
d_'43''45'isMonoidMonomorphism_1230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_986 -> T_IsMonoidMonomorphism_372
d_'43''45'isMonoidMonomorphism_1230 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isMonoidMonomorphism_1230 v7
du_'43''45'isMonoidMonomorphism_1230 ::
  T_IsNearSemiringIsomorphism_986 -> T_IsMonoidMonomorphism_372
du_'43''45'isMonoidMonomorphism_1230 v0
  = coe
      du_'43''45'isMonoidMonomorphism_974
      (coe d_isNearSemiringMonomorphism_994 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism.ε-homo
d_ε'45'homo_1232 :: T_IsNearSemiringIsomorphism_986 -> AgdaAny
d_ε'45'homo_1232 v0
  = coe
      d_ε'45'homo_360
      (coe
         d_'43''45'isMonoidHomomorphism_924
         (coe
            d_isNearSemiringHomomorphism_952
            (coe d_isNearSemiringMonomorphism_994 (coe v0))))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism.injective
d_injective_1234 ::
  T_IsNearSemiringIsomorphism_986 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_1234 v0
  = coe
      d_injective_954 (coe d_isNearSemiringMonomorphism_994 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_1236 ::
  T_IsNearSemiringIsomorphism_986 -> T_IsNearSemiringHomomorphism_916
d_isNearSemiringHomomorphism_1236 v0
  = coe
      d_isNearSemiringHomomorphism_952
      (coe d_isNearSemiringMonomorphism_994 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism.isNearSemiringMonomorphism
d_isNearSemiringMonomorphism_1238 ::
  T_IsNearSemiringIsomorphism_986 -> T_IsNearSemiringMonomorphism_944
d_isNearSemiringMonomorphism_1238 v0
  = coe d_isNearSemiringMonomorphism_994 (coe v0)
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism.isRelHomomorphism
d_isRelHomomorphism_1240 ::
  T_IsNearSemiringIsomorphism_986 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1240 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_'43''45'isMonoidHomomorphism_924
            (coe
               d_isNearSemiringHomomorphism_952
               (coe d_isNearSemiringMonomorphism_994 (coe v0)))))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism.isRelIsomorphism
d_isRelIsomorphism_1242 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_986 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
d_isRelIsomorphism_1242 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelIsomorphism_1242 v7
du_isRelIsomorphism_1242 ::
  T_IsNearSemiringIsomorphism_986 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
du_isRelIsomorphism_1242 v0
  = let v1 = coe du_'43''45'isMonoidIsomorphism_1028 (coe v0) in
    coe
      (coe
         du_isRelIsomorphism_244 (coe du_isMagmaIsomorphism_436 (coe v1)))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism.isRelMonomorphism
d_isRelMonomorphism_1244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_986 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_1244 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_1244 v7
du_isRelMonomorphism_1244 ::
  T_IsNearSemiringIsomorphism_986 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_1244 v0
  = let v1 = d_isNearSemiringMonomorphism_994 (coe v0) in
    coe
      (let v2 = coe du_'43''45'isMonoidMonomorphism_974 (coe v1) in
       coe
         (coe
            du_isRelMonomorphism_214
            (coe du_isMagmaMonomorphism_396 (coe v2))))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism.surjective
d_surjective_1246 ::
  T_IsNearSemiringIsomorphism_986 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_1246 v0 = coe d_surjective_996 (coe v0)
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism.cong
d_cong_1248 ::
  T_IsNearSemiringIsomorphism_986 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1248 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe
               d_'43''45'isMonoidHomomorphism_924
               (coe
                  d_isNearSemiringHomomorphism_952
                  (coe d_isNearSemiringMonomorphism_994 (coe v0))))))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringMonomorphism.*-homo
d_'42''45'homo_1252 ::
  T_IsNearSemiringMonomorphism_944 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_1252 v0
  = coe
      d_'42''45'homo_926 (coe d_isNearSemiringHomomorphism_952 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringMonomorphism.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_1254 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringMonomorphism_944 -> T_IsMagmaHomomorphism_176
d_'42''45'isMagmaHomomorphism_1254 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_1254 v7
du_'42''45'isMagmaHomomorphism_1254 ::
  T_IsNearSemiringMonomorphism_944 -> T_IsMagmaHomomorphism_176
du_'42''45'isMagmaHomomorphism_1254 v0
  = coe
      du_'42''45'isMagmaHomomorphism_940
      (coe d_isNearSemiringHomomorphism_952 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringMonomorphism.*-isMagmaMonomorphism
d_'42''45'isMagmaMonomorphism_1256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringMonomorphism_944 -> T_IsMagmaMonomorphism_194
d_'42''45'isMagmaMonomorphism_1256 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'42''45'isMagmaMonomorphism_1256
du_'42''45'isMagmaMonomorphism_1256 ::
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringMonomorphism_944 -> T_IsMagmaMonomorphism_194
du_'42''45'isMagmaMonomorphism_1256 v0 v1
  = coe du_'42''45'isMagmaMonomorphism_982 v1
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringMonomorphism.homo
d_homo_1258 ::
  T_IsNearSemiringMonomorphism_944 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1258 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_'43''45'isMonoidHomomorphism_924
            (coe d_isNearSemiringHomomorphism_952 (coe v0))))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_1260 ::
  T_IsNearSemiringMonomorphism_944 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_1260 v0
  = coe
      d_isMagmaHomomorphism_358
      (coe
         d_'43''45'isMonoidHomomorphism_924
         (coe d_isNearSemiringHomomorphism_952 (coe v0)))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringMonomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_1262 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringMonomorphism_944 -> T_IsMagmaMonomorphism_194
d_isMagmaMonomorphism_1262 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_1262 v7
du_isMagmaMonomorphism_1262 ::
  T_IsNearSemiringMonomorphism_944 -> T_IsMagmaMonomorphism_194
du_isMagmaMonomorphism_1262 v0
  = coe
      du_isMagmaMonomorphism_396
      (coe du_'43''45'isMonoidMonomorphism_974 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringMonomorphism.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_1264 ::
  T_IsNearSemiringMonomorphism_944 -> T_IsMonoidHomomorphism_350
d_'43''45'isMonoidHomomorphism_1264 v0
  = coe
      d_'43''45'isMonoidHomomorphism_924
      (coe d_isNearSemiringHomomorphism_952 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringMonomorphism.+-isMonoidMonomorphism
d_'43''45'isMonoidMonomorphism_1266 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringMonomorphism_944 -> T_IsMonoidMonomorphism_372
d_'43''45'isMonoidMonomorphism_1266 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'43''45'isMonoidMonomorphism_1266
du_'43''45'isMonoidMonomorphism_1266 ::
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringMonomorphism_944 -> T_IsMonoidMonomorphism_372
du_'43''45'isMonoidMonomorphism_1266 v0 v1
  = coe du_'43''45'isMonoidMonomorphism_974 v1
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringMonomorphism.ε-homo
d_ε'45'homo_1268 :: T_IsNearSemiringMonomorphism_944 -> AgdaAny
d_ε'45'homo_1268 v0
  = coe
      d_ε'45'homo_360
      (coe
         d_'43''45'isMonoidHomomorphism_924
         (coe d_isNearSemiringHomomorphism_952 (coe v0)))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringMonomorphism.injective
d_injective_1270 ::
  T_IsNearSemiringMonomorphism_944 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_1270 v0 = coe d_injective_954 (coe v0)
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringMonomorphism.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_1272 ::
  T_IsNearSemiringMonomorphism_944 ->
  T_IsNearSemiringHomomorphism_916
d_isNearSemiringHomomorphism_1272 v0
  = coe d_isNearSemiringHomomorphism_952 (coe v0)
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringMonomorphism.isRelHomomorphism
d_isRelHomomorphism_1274 ::
  T_IsNearSemiringMonomorphism_944 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1274 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_'43''45'isMonoidHomomorphism_924
            (coe d_isNearSemiringHomomorphism_952 (coe v0))))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringMonomorphism.isRelMonomorphism
d_isRelMonomorphism_1276 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringMonomorphism_944 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_1276 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_1276 v7
du_isRelMonomorphism_1276 ::
  T_IsNearSemiringMonomorphism_944 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_1276 v0
  = let v1 = coe du_'43''45'isMonoidMonomorphism_974 (coe v0) in
    coe
      (coe
         du_isRelMonomorphism_214 (coe du_isMagmaMonomorphism_396 (coe v1)))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringMonomorphism.cong
d_cong_1278 ::
  T_IsNearSemiringMonomorphism_944 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1278 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe
               d_'43''45'isMonoidHomomorphism_924
               (coe d_isNearSemiringHomomorphism_952 (coe v0)))))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringHomomorphism
d_IsSemiringHomomorphism_1282 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsSemiringHomomorphism_1282
  = C_IsSemiringHomomorphism'46'constructor_26561 T_IsNearSemiringHomomorphism_916
                                                  AgdaAny
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringHomomorphism.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_1290 ::
  T_IsSemiringHomomorphism_1282 -> T_IsNearSemiringHomomorphism_916
d_isNearSemiringHomomorphism_1290 v0
  = case coe v0 of
      C_IsSemiringHomomorphism'46'constructor_26561 v1 v2 -> coe v1
      _                                                   -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringHomomorphism.1#-homo
d_1'35''45'homo_1292 :: T_IsSemiringHomomorphism_1282 -> AgdaAny
d_1'35''45'homo_1292 v0
  = case coe v0 of
      C_IsSemiringHomomorphism'46'constructor_26561 v1 v2 -> coe v2
      _                                                   -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringHomomorphism._.*-homo
d_'42''45'homo_1296 ::
  T_IsSemiringHomomorphism_1282 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_1296 v0
  = coe
      d_'42''45'homo_926 (coe d_isNearSemiringHomomorphism_1290 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringHomomorphism._.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_1298 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringHomomorphism_1282 -> T_IsMagmaHomomorphism_176
d_'42''45'isMagmaHomomorphism_1298 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_1298 v7
du_'42''45'isMagmaHomomorphism_1298 ::
  T_IsSemiringHomomorphism_1282 -> T_IsMagmaHomomorphism_176
du_'42''45'isMagmaHomomorphism_1298 v0
  = coe
      du_'42''45'isMagmaHomomorphism_940
      (coe d_isNearSemiringHomomorphism_1290 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringHomomorphism._.homo
d_homo_1300 ::
  T_IsSemiringHomomorphism_1282 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1300 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_'43''45'isMonoidHomomorphism_924
            (coe d_isNearSemiringHomomorphism_1290 (coe v0))))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringHomomorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_1302 ::
  T_IsSemiringHomomorphism_1282 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_1302 v0
  = coe
      d_isMagmaHomomorphism_358
      (coe
         d_'43''45'isMonoidHomomorphism_924
         (coe d_isNearSemiringHomomorphism_1290 (coe v0)))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringHomomorphism._.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_1304 ::
  T_IsSemiringHomomorphism_1282 -> T_IsMonoidHomomorphism_350
d_'43''45'isMonoidHomomorphism_1304 v0
  = coe
      d_'43''45'isMonoidHomomorphism_924
      (coe d_isNearSemiringHomomorphism_1290 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringHomomorphism._.ε-homo
d_ε'45'homo_1306 :: T_IsSemiringHomomorphism_1282 -> AgdaAny
d_ε'45'homo_1306 v0
  = coe
      d_ε'45'homo_360
      (coe
         d_'43''45'isMonoidHomomorphism_924
         (coe d_isNearSemiringHomomorphism_1290 (coe v0)))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringHomomorphism._.isRelHomomorphism
d_isRelHomomorphism_1308 ::
  T_IsSemiringHomomorphism_1282 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1308 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_'43''45'isMonoidHomomorphism_924
            (coe d_isNearSemiringHomomorphism_1290 (coe v0))))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringHomomorphism._.cong
d_cong_1310 ::
  T_IsSemiringHomomorphism_1282 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1310 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe
               d_'43''45'isMonoidHomomorphism_924
               (coe d_isNearSemiringHomomorphism_1290 (coe v0)))))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringHomomorphism.*-isMonoidHomomorphism
d_'42''45'isMonoidHomomorphism_1312 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringHomomorphism_1282 -> T_IsMonoidHomomorphism_350
d_'42''45'isMonoidHomomorphism_1312 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidHomomorphism_1312 v7
du_'42''45'isMonoidHomomorphism_1312 ::
  T_IsSemiringHomomorphism_1282 -> T_IsMonoidHomomorphism_350
du_'42''45'isMonoidHomomorphism_1312 v0
  = coe
      C_IsMonoidHomomorphism'46'constructor_9411
      (coe
         du_'42''45'isMagmaHomomorphism_940
         (coe d_isNearSemiringHomomorphism_1290 (coe v0)))
      (coe d_1'35''45'homo_1292 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringMonomorphism
d_IsSemiringMonomorphism_1316 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsSemiringMonomorphism_1316
  = C_IsSemiringMonomorphism'46'constructor_27871 T_IsSemiringHomomorphism_1282
                                                  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringMonomorphism.isSemiringHomomorphism
d_isSemiringHomomorphism_1324 ::
  T_IsSemiringMonomorphism_1316 -> T_IsSemiringHomomorphism_1282
d_isSemiringHomomorphism_1324 v0
  = case coe v0 of
      C_IsSemiringMonomorphism'46'constructor_27871 v1 v2 -> coe v1
      _                                                   -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringMonomorphism.injective
d_injective_1326 ::
  T_IsSemiringMonomorphism_1316 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_1326 v0
  = case coe v0 of
      C_IsSemiringMonomorphism'46'constructor_27871 v1 v2 -> coe v2
      _                                                   -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringMonomorphism._.*-homo
d_'42''45'homo_1330 ::
  T_IsSemiringMonomorphism_1316 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_1330 v0
  = coe
      d_'42''45'homo_926
      (coe
         d_isNearSemiringHomomorphism_1290
         (coe d_isSemiringHomomorphism_1324 (coe v0)))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringMonomorphism._.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_1332 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1316 -> T_IsMagmaHomomorphism_176
d_'42''45'isMagmaHomomorphism_1332 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_1332 v7
du_'42''45'isMagmaHomomorphism_1332 ::
  T_IsSemiringMonomorphism_1316 -> T_IsMagmaHomomorphism_176
du_'42''45'isMagmaHomomorphism_1332 v0
  = let v1 = d_isSemiringHomomorphism_1324 (coe v0) in
    coe
      (coe
         du_'42''45'isMagmaHomomorphism_940
         (coe d_isNearSemiringHomomorphism_1290 (coe v1)))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringMonomorphism._.*-isMonoidHomomorphism
d_'42''45'isMonoidHomomorphism_1334 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1316 -> T_IsMonoidHomomorphism_350
d_'42''45'isMonoidHomomorphism_1334 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidHomomorphism_1334 v7
du_'42''45'isMonoidHomomorphism_1334 ::
  T_IsSemiringMonomorphism_1316 -> T_IsMonoidHomomorphism_350
du_'42''45'isMonoidHomomorphism_1334 v0
  = coe
      du_'42''45'isMonoidHomomorphism_1312
      (coe d_isSemiringHomomorphism_1324 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringMonomorphism._.homo
d_homo_1336 ::
  T_IsSemiringMonomorphism_1316 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1336 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_'43''45'isMonoidHomomorphism_924
            (coe
               d_isNearSemiringHomomorphism_1290
               (coe d_isSemiringHomomorphism_1324 (coe v0)))))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringMonomorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_1338 ::
  T_IsSemiringMonomorphism_1316 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_1338 v0
  = coe
      d_isMagmaHomomorphism_358
      (coe
         d_'43''45'isMonoidHomomorphism_924
         (coe
            d_isNearSemiringHomomorphism_1290
            (coe d_isSemiringHomomorphism_1324 (coe v0))))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringMonomorphism._.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_1340 ::
  T_IsSemiringMonomorphism_1316 -> T_IsMonoidHomomorphism_350
d_'43''45'isMonoidHomomorphism_1340 v0
  = coe
      d_'43''45'isMonoidHomomorphism_924
      (coe
         d_isNearSemiringHomomorphism_1290
         (coe d_isSemiringHomomorphism_1324 (coe v0)))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringMonomorphism._.ε-homo
d_ε'45'homo_1342 :: T_IsSemiringMonomorphism_1316 -> AgdaAny
d_ε'45'homo_1342 v0
  = coe
      d_ε'45'homo_360
      (coe
         d_'43''45'isMonoidHomomorphism_924
         (coe
            d_isNearSemiringHomomorphism_1290
            (coe d_isSemiringHomomorphism_1324 (coe v0))))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringMonomorphism._.1#-homo
d_1'35''45'homo_1344 :: T_IsSemiringMonomorphism_1316 -> AgdaAny
d_1'35''45'homo_1344 v0
  = coe
      d_1'35''45'homo_1292 (coe d_isSemiringHomomorphism_1324 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringMonomorphism._.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_1346 ::
  T_IsSemiringMonomorphism_1316 -> T_IsNearSemiringHomomorphism_916
d_isNearSemiringHomomorphism_1346 v0
  = coe
      d_isNearSemiringHomomorphism_1290
      (coe d_isSemiringHomomorphism_1324 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringMonomorphism._.isRelHomomorphism
d_isRelHomomorphism_1348 ::
  T_IsSemiringMonomorphism_1316 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1348 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_'43''45'isMonoidHomomorphism_924
            (coe
               d_isNearSemiringHomomorphism_1290
               (coe d_isSemiringHomomorphism_1324 (coe v0)))))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringMonomorphism._.cong
d_cong_1350 ::
  T_IsSemiringMonomorphism_1316 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1350 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe
               d_'43''45'isMonoidHomomorphism_924
               (coe
                  d_isNearSemiringHomomorphism_1290
                  (coe d_isSemiringHomomorphism_1324 (coe v0))))))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringMonomorphism.isNearSemiringMonomorphism
d_isNearSemiringMonomorphism_1352 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1316 -> T_IsNearSemiringMonomorphism_944
d_isNearSemiringMonomorphism_1352 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isNearSemiringMonomorphism_1352 v7
du_isNearSemiringMonomorphism_1352 ::
  T_IsSemiringMonomorphism_1316 -> T_IsNearSemiringMonomorphism_944
du_isNearSemiringMonomorphism_1352 v0
  = coe
      C_IsNearSemiringMonomorphism'46'constructor_21119
      (coe
         d_isNearSemiringHomomorphism_1290
         (coe d_isSemiringHomomorphism_1324 (coe v0)))
      (coe d_injective_1326 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringMonomorphism._.*-isMagmaMonomorphism
d_'42''45'isMagmaMonomorphism_1356 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1316 -> T_IsMagmaMonomorphism_194
d_'42''45'isMagmaMonomorphism_1356 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaMonomorphism_1356 v7
du_'42''45'isMagmaMonomorphism_1356 ::
  T_IsSemiringMonomorphism_1316 -> T_IsMagmaMonomorphism_194
du_'42''45'isMagmaMonomorphism_1356 v0
  = coe
      du_'42''45'isMagmaMonomorphism_982
      (coe du_isNearSemiringMonomorphism_1352 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringMonomorphism._.+-isMonoidMonomorphism
d_'43''45'isMonoidMonomorphism_1358 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1316 -> T_IsMonoidMonomorphism_372
d_'43''45'isMonoidMonomorphism_1358 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isMonoidMonomorphism_1358 v7
du_'43''45'isMonoidMonomorphism_1358 ::
  T_IsSemiringMonomorphism_1316 -> T_IsMonoidMonomorphism_372
du_'43''45'isMonoidMonomorphism_1358 v0
  = coe
      du_'43''45'isMonoidMonomorphism_974
      (coe du_isNearSemiringMonomorphism_1352 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringMonomorphism.*-isMonoidMonomorphism
d_'42''45'isMonoidMonomorphism_1360 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1316 -> T_IsMonoidMonomorphism_372
d_'42''45'isMonoidMonomorphism_1360 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidMonomorphism_1360 v7
du_'42''45'isMonoidMonomorphism_1360 ::
  T_IsSemiringMonomorphism_1316 -> T_IsMonoidMonomorphism_372
du_'42''45'isMonoidMonomorphism_1360 v0
  = coe
      C_IsMonoidMonomorphism'46'constructor_10237
      (coe
         du_'42''45'isMonoidHomomorphism_1312
         (coe d_isSemiringHomomorphism_1324 (coe v0)))
      (coe d_injective_1326 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism
d_IsSemiringIsomorphism_1364 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsSemiringIsomorphism_1364
  = C_IsSemiringIsomorphism'46'constructor_29931 T_IsSemiringMonomorphism_1316
                                                 (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism.isSemiringMonomorphism
d_isSemiringMonomorphism_1372 ::
  T_IsSemiringIsomorphism_1364 -> T_IsSemiringMonomorphism_1316
d_isSemiringMonomorphism_1372 v0
  = case coe v0 of
      C_IsSemiringIsomorphism'46'constructor_29931 v1 v2 -> coe v1
      _                                                  -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism.surjective
d_surjective_1374 ::
  T_IsSemiringIsomorphism_1364 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_1374 v0
  = case coe v0 of
      C_IsSemiringIsomorphism'46'constructor_29931 v1 v2 -> coe v2
      _                                                  -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism._.*-homo
d_'42''45'homo_1378 ::
  T_IsSemiringIsomorphism_1364 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_1378 v0
  = coe
      d_'42''45'homo_926
      (coe
         d_isNearSemiringHomomorphism_1290
         (coe
            d_isSemiringHomomorphism_1324
            (coe d_isSemiringMonomorphism_1372 (coe v0))))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism._.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_1380 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1364 -> T_IsMagmaHomomorphism_176
d_'42''45'isMagmaHomomorphism_1380 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_1380 v7
du_'42''45'isMagmaHomomorphism_1380 ::
  T_IsSemiringIsomorphism_1364 -> T_IsMagmaHomomorphism_176
du_'42''45'isMagmaHomomorphism_1380 v0
  = let v1 = d_isSemiringMonomorphism_1372 (coe v0) in
    coe
      (let v2 = d_isSemiringHomomorphism_1324 (coe v1) in
       coe
         (coe
            du_'42''45'isMagmaHomomorphism_940
            (coe d_isNearSemiringHomomorphism_1290 (coe v2))))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism._.*-isMagmaMonomorphism
d_'42''45'isMagmaMonomorphism_1382 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1364 -> T_IsMagmaMonomorphism_194
d_'42''45'isMagmaMonomorphism_1382 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaMonomorphism_1382 v7
du_'42''45'isMagmaMonomorphism_1382 ::
  T_IsSemiringIsomorphism_1364 -> T_IsMagmaMonomorphism_194
du_'42''45'isMagmaMonomorphism_1382 v0
  = let v1 = d_isSemiringMonomorphism_1372 (coe v0) in
    coe
      (coe
         du_'42''45'isMagmaMonomorphism_982
         (coe du_isNearSemiringMonomorphism_1352 (coe v1)))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism._.*-isMonoidHomomorphism
d_'42''45'isMonoidHomomorphism_1384 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1364 -> T_IsMonoidHomomorphism_350
d_'42''45'isMonoidHomomorphism_1384 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidHomomorphism_1384 v7
du_'42''45'isMonoidHomomorphism_1384 ::
  T_IsSemiringIsomorphism_1364 -> T_IsMonoidHomomorphism_350
du_'42''45'isMonoidHomomorphism_1384 v0
  = let v1 = d_isSemiringMonomorphism_1372 (coe v0) in
    coe
      (coe
         du_'42''45'isMonoidHomomorphism_1312
         (coe d_isSemiringHomomorphism_1324 (coe v1)))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism._.*-isMonoidMonomorphism
d_'42''45'isMonoidMonomorphism_1386 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1364 -> T_IsMonoidMonomorphism_372
d_'42''45'isMonoidMonomorphism_1386 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidMonomorphism_1386 v7
du_'42''45'isMonoidMonomorphism_1386 ::
  T_IsSemiringIsomorphism_1364 -> T_IsMonoidMonomorphism_372
du_'42''45'isMonoidMonomorphism_1386 v0
  = coe
      du_'42''45'isMonoidMonomorphism_1360
      (coe d_isSemiringMonomorphism_1372 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism._.homo
d_homo_1388 ::
  T_IsSemiringIsomorphism_1364 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1388 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_'43''45'isMonoidHomomorphism_924
            (coe
               d_isNearSemiringHomomorphism_1290
               (coe
                  d_isSemiringHomomorphism_1324
                  (coe d_isSemiringMonomorphism_1372 (coe v0))))))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_1390 ::
  T_IsSemiringIsomorphism_1364 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_1390 v0
  = coe
      d_isMagmaHomomorphism_358
      (coe
         d_'43''45'isMonoidHomomorphism_924
         (coe
            d_isNearSemiringHomomorphism_1290
            (coe
               d_isSemiringHomomorphism_1324
               (coe d_isSemiringMonomorphism_1372 (coe v0)))))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism._.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_1392 ::
  T_IsSemiringIsomorphism_1364 -> T_IsMonoidHomomorphism_350
d_'43''45'isMonoidHomomorphism_1392 v0
  = coe
      d_'43''45'isMonoidHomomorphism_924
      (coe
         d_isNearSemiringHomomorphism_1290
         (coe
            d_isSemiringHomomorphism_1324
            (coe d_isSemiringMonomorphism_1372 (coe v0))))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism._.+-isMonoidMonomorphism
d_'43''45'isMonoidMonomorphism_1394 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1364 -> T_IsMonoidMonomorphism_372
d_'43''45'isMonoidMonomorphism_1394 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isMonoidMonomorphism_1394 v7
du_'43''45'isMonoidMonomorphism_1394 ::
  T_IsSemiringIsomorphism_1364 -> T_IsMonoidMonomorphism_372
du_'43''45'isMonoidMonomorphism_1394 v0
  = let v1 = d_isSemiringMonomorphism_1372 (coe v0) in
    coe
      (coe
         du_'43''45'isMonoidMonomorphism_974
         (coe du_isNearSemiringMonomorphism_1352 (coe v1)))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism._.ε-homo
d_ε'45'homo_1396 :: T_IsSemiringIsomorphism_1364 -> AgdaAny
d_ε'45'homo_1396 v0
  = coe
      d_ε'45'homo_360
      (coe
         d_'43''45'isMonoidHomomorphism_924
         (coe
            d_isNearSemiringHomomorphism_1290
            (coe
               d_isSemiringHomomorphism_1324
               (coe d_isSemiringMonomorphism_1372 (coe v0)))))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism._.1#-homo
d_1'35''45'homo_1398 :: T_IsSemiringIsomorphism_1364 -> AgdaAny
d_1'35''45'homo_1398 v0
  = coe
      d_1'35''45'homo_1292
      (coe
         d_isSemiringHomomorphism_1324
         (coe d_isSemiringMonomorphism_1372 (coe v0)))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism._.injective
d_injective_1400 ::
  T_IsSemiringIsomorphism_1364 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_1400 v0
  = coe d_injective_1326 (coe d_isSemiringMonomorphism_1372 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism._.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_1402 ::
  T_IsSemiringIsomorphism_1364 -> T_IsNearSemiringHomomorphism_916
d_isNearSemiringHomomorphism_1402 v0
  = coe
      d_isNearSemiringHomomorphism_1290
      (coe
         d_isSemiringHomomorphism_1324
         (coe d_isSemiringMonomorphism_1372 (coe v0)))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism._.isNearSemiringMonomorphism
d_isNearSemiringMonomorphism_1404 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1364 -> T_IsNearSemiringMonomorphism_944
d_isNearSemiringMonomorphism_1404 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isNearSemiringMonomorphism_1404 v7
du_isNearSemiringMonomorphism_1404 ::
  T_IsSemiringIsomorphism_1364 -> T_IsNearSemiringMonomorphism_944
du_isNearSemiringMonomorphism_1404 v0
  = coe
      du_isNearSemiringMonomorphism_1352
      (coe d_isSemiringMonomorphism_1372 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism._.isRelHomomorphism
d_isRelHomomorphism_1406 ::
  T_IsSemiringIsomorphism_1364 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1406 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_'43''45'isMonoidHomomorphism_924
            (coe
               d_isNearSemiringHomomorphism_1290
               (coe
                  d_isSemiringHomomorphism_1324
                  (coe d_isSemiringMonomorphism_1372 (coe v0))))))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism._.isSemiringHomomorphism
d_isSemiringHomomorphism_1408 ::
  T_IsSemiringIsomorphism_1364 -> T_IsSemiringHomomorphism_1282
d_isSemiringHomomorphism_1408 v0
  = coe
      d_isSemiringHomomorphism_1324
      (coe d_isSemiringMonomorphism_1372 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism._.cong
d_cong_1410 ::
  T_IsSemiringIsomorphism_1364 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1410 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe
               d_'43''45'isMonoidHomomorphism_924
               (coe
                  d_isNearSemiringHomomorphism_1290
                  (coe
                     d_isSemiringHomomorphism_1324
                     (coe d_isSemiringMonomorphism_1372 (coe v0)))))))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism.isNearSemiringIsomorphism
d_isNearSemiringIsomorphism_1412 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1364 -> T_IsNearSemiringIsomorphism_986
d_isNearSemiringIsomorphism_1412 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isNearSemiringIsomorphism_1412 v7
du_isNearSemiringIsomorphism_1412 ::
  T_IsSemiringIsomorphism_1364 -> T_IsNearSemiringIsomorphism_986
du_isNearSemiringIsomorphism_1412 v0
  = coe
      C_IsNearSemiringIsomorphism'46'constructor_23007
      (coe
         du_isNearSemiringMonomorphism_1352
         (coe d_isSemiringMonomorphism_1372 (coe v0)))
      (coe d_surjective_1374 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism._.*-isMagmaIsomorphism
d_'42''45'isMagmaIsomorphism_1416 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1364 -> T_IsMagmaIsomorphism_218
d_'42''45'isMagmaIsomorphism_1416 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaIsomorphism_1416 v7
du_'42''45'isMagmaIsomorphism_1416 ::
  T_IsSemiringIsomorphism_1364 -> T_IsMagmaIsomorphism_218
du_'42''45'isMagmaIsomorphism_1416 v0
  = coe
      du_'42''45'isMagmaIsomorphism_1036
      (coe du_isNearSemiringIsomorphism_1412 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism._.+-isMonoidIsomorphism
d_'43''45'isMonoidIsomorphism_1418 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1364 -> T_IsMonoidIsomorphism_404
d_'43''45'isMonoidIsomorphism_1418 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isMonoidIsomorphism_1418 v7
du_'43''45'isMonoidIsomorphism_1418 ::
  T_IsSemiringIsomorphism_1364 -> T_IsMonoidIsomorphism_404
du_'43''45'isMonoidIsomorphism_1418 v0
  = coe
      du_'43''45'isMonoidIsomorphism_1028
      (coe du_isNearSemiringIsomorphism_1412 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism.*-isMonoidIsomorphism
d_'42''45'isMonoidIsomorphism_1420 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1364 -> T_IsMonoidIsomorphism_404
d_'42''45'isMonoidIsomorphism_1420 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidIsomorphism_1420 v7
du_'42''45'isMonoidIsomorphism_1420 ::
  T_IsSemiringIsomorphism_1364 -> T_IsMonoidIsomorphism_404
du_'42''45'isMonoidIsomorphism_1420 v0
  = coe
      C_IsMonoidIsomorphism'46'constructor_11597
      (coe
         du_'42''45'isMonoidMonomorphism_1360
         (coe d_isSemiringMonomorphism_1372 (coe v0)))
      (coe d_surjective_1374 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms._._*_
d__'42'__1438 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'42'__1438 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du__'42'__1438 v4
du__'42'__1438 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'42'__1438 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__246 (coe v0)
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms._._≈_
d__'8776'__1442 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__1442 = erased
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms._.Carrier
d_Carrier_1458 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 -> ()
d_Carrier_1458 = erased
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupHomomorphism
d_IsGroupHomomorphism_1486 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupIsomorphism
d_IsGroupIsomorphism_1488 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupMonomorphism
d_IsGroupMonomorphism_1490 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupHomomorphism.homo
d_homo_1494 ::
  T_IsGroupHomomorphism_622 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1494 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe d_isMonoidHomomorphism_630 (coe v0)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupHomomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_1496 ::
  T_IsGroupHomomorphism_622 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_1496 v0
  = coe
      d_isMagmaHomomorphism_358 (coe d_isMonoidHomomorphism_630 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupHomomorphism.isMonoidHomomorphism
d_isMonoidHomomorphism_1498 ::
  T_IsGroupHomomorphism_622 -> T_IsMonoidHomomorphism_350
d_isMonoidHomomorphism_1498 v0
  = coe d_isMonoidHomomorphism_630 (coe v0)
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupHomomorphism.isRelHomomorphism
d_isRelHomomorphism_1500 ::
  T_IsGroupHomomorphism_622 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1500 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe d_isMonoidHomomorphism_630 (coe v0)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupHomomorphism.ε-homo
d_ε'45'homo_1502 :: T_IsGroupHomomorphism_622 -> AgdaAny
d_ε'45'homo_1502 v0
  = coe d_ε'45'homo_360 (coe d_isMonoidHomomorphism_630 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupHomomorphism.⁻¹-homo
d_'8315''185''45'homo_1504 ::
  T_IsGroupHomomorphism_622 -> AgdaAny -> AgdaAny
d_'8315''185''45'homo_1504 v0
  = coe d_'8315''185''45'homo_632 (coe v0)
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupHomomorphism.cong
d_cong_1506 ::
  T_IsGroupHomomorphism_622 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1506 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe d_isMonoidHomomorphism_630 (coe v0))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupIsomorphism.injective
d_injective_1510 ::
  T_IsGroupIsomorphism_686 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_1510 v0
  = coe d_injective_658 (coe d_isGroupMonomorphism_694 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupIsomorphism.isGroupHomomorphism
d_isGroupHomomorphism_1512 ::
  T_IsGroupIsomorphism_686 -> T_IsGroupHomomorphism_622
d_isGroupHomomorphism_1512 v0
  = coe
      d_isGroupHomomorphism_656 (coe d_isGroupMonomorphism_694 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupIsomorphism.isGroupMonomorphism
d_isGroupMonomorphism_1514 ::
  T_IsGroupIsomorphism_686 -> T_IsGroupMonomorphism_648
d_isGroupMonomorphism_1514 v0
  = coe d_isGroupMonomorphism_694 (coe v0)
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupIsomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_1516 ::
  T_IsGroupIsomorphism_686 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_1516 v0
  = coe
      d_isMagmaHomomorphism_358
      (coe
         d_isMonoidHomomorphism_630
         (coe
            d_isGroupHomomorphism_656
            (coe d_isGroupMonomorphism_694 (coe v0))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupIsomorphism.isMagmaIsomorphism
d_isMagmaIsomorphism_1518 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupIsomorphism_686 -> T_IsMagmaIsomorphism_218
d_isMagmaIsomorphism_1518 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaIsomorphism_1518 v7
du_isMagmaIsomorphism_1518 ::
  T_IsGroupIsomorphism_686 -> T_IsMagmaIsomorphism_218
du_isMagmaIsomorphism_1518 v0
  = coe
      du_isMagmaIsomorphism_436 (coe du_isMonoidIsomorphism_724 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupIsomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_1520 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupIsomorphism_686 -> T_IsMagmaMonomorphism_194
d_isMagmaMonomorphism_1520 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_1520 v7
du_isMagmaMonomorphism_1520 ::
  T_IsGroupIsomorphism_686 -> T_IsMagmaMonomorphism_194
du_isMagmaMonomorphism_1520 v0
  = let v1 = d_isGroupMonomorphism_694 (coe v0) in
    coe
      (coe
         du_isMagmaMonomorphism_396
         (coe du_isMonoidMonomorphism_676 (coe v1)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupIsomorphism.isMonoidHomomorphism
d_isMonoidHomomorphism_1522 ::
  T_IsGroupIsomorphism_686 -> T_IsMonoidHomomorphism_350
d_isMonoidHomomorphism_1522 v0
  = coe
      d_isMonoidHomomorphism_630
      (coe
         d_isGroupHomomorphism_656 (coe d_isGroupMonomorphism_694 (coe v0)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupIsomorphism.isMonoidIsomorphism
d_isMonoidIsomorphism_1524 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupIsomorphism_686 -> T_IsMonoidIsomorphism_404
d_isMonoidIsomorphism_1524 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isMonoidIsomorphism_1524
du_isMonoidIsomorphism_1524 ::
  (AgdaAny -> AgdaAny) ->
  T_IsGroupIsomorphism_686 -> T_IsMonoidIsomorphism_404
du_isMonoidIsomorphism_1524 v0 v1
  = coe du_isMonoidIsomorphism_724 v1
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupIsomorphism.isMonoidMonomorphism
d_isMonoidMonomorphism_1526 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupIsomorphism_686 -> T_IsMonoidMonomorphism_372
d_isMonoidMonomorphism_1526 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMonoidMonomorphism_1526 v7
du_isMonoidMonomorphism_1526 ::
  T_IsGroupIsomorphism_686 -> T_IsMonoidMonomorphism_372
du_isMonoidMonomorphism_1526 v0
  = coe
      du_isMonoidMonomorphism_676
      (coe d_isGroupMonomorphism_694 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupIsomorphism.isRelHomomorphism
d_isRelHomomorphism_1528 ::
  T_IsGroupIsomorphism_686 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1528 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_isMonoidHomomorphism_630
            (coe
               d_isGroupHomomorphism_656
               (coe d_isGroupMonomorphism_694 (coe v0)))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupIsomorphism.isRelIsomorphism
d_isRelIsomorphism_1530 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupIsomorphism_686 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
d_isRelIsomorphism_1530 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelIsomorphism_1530 v7
du_isRelIsomorphism_1530 ::
  T_IsGroupIsomorphism_686 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
du_isRelIsomorphism_1530 v0
  = let v1 = coe du_isMonoidIsomorphism_724 (coe v0) in
    coe
      (coe
         du_isRelIsomorphism_244 (coe du_isMagmaIsomorphism_436 (coe v1)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupIsomorphism.isRelMonomorphism
d_isRelMonomorphism_1532 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupIsomorphism_686 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_1532 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_1532 v7
du_isRelMonomorphism_1532 ::
  T_IsGroupIsomorphism_686 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_1532 v0
  = let v1 = d_isGroupMonomorphism_694 (coe v0) in
    coe
      (let v2 = coe du_isMonoidMonomorphism_676 (coe v1) in
       coe
         (coe
            du_isRelMonomorphism_214
            (coe du_isMagmaMonomorphism_396 (coe v2))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupIsomorphism.surjective
d_surjective_1534 ::
  T_IsGroupIsomorphism_686 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_1534 v0 = coe d_surjective_696 (coe v0)
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupIsomorphism.ε-homo
d_ε'45'homo_1536 :: T_IsGroupIsomorphism_686 -> AgdaAny
d_ε'45'homo_1536 v0
  = coe
      d_ε'45'homo_360
      (coe
         d_isMonoidHomomorphism_630
         (coe
            d_isGroupHomomorphism_656
            (coe d_isGroupMonomorphism_694 (coe v0))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupIsomorphism.⁻¹-homo
d_'8315''185''45'homo_1538 ::
  T_IsGroupIsomorphism_686 -> AgdaAny -> AgdaAny
d_'8315''185''45'homo_1538 v0
  = coe
      d_'8315''185''45'homo_632
      (coe
         d_isGroupHomomorphism_656 (coe d_isGroupMonomorphism_694 (coe v0)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupIsomorphism.homo
d_homo_1540 ::
  T_IsGroupIsomorphism_686 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1540 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_isMonoidHomomorphism_630
            (coe
               d_isGroupHomomorphism_656
               (coe d_isGroupMonomorphism_694 (coe v0)))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupIsomorphism.cong
d_cong_1542 ::
  T_IsGroupIsomorphism_686 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1542 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe
               d_isMonoidHomomorphism_630
               (coe
                  d_isGroupHomomorphism_656
                  (coe d_isGroupMonomorphism_694 (coe v0))))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupMonomorphism.injective
d_injective_1546 ::
  T_IsGroupMonomorphism_648 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_1546 v0 = coe d_injective_658 (coe v0)
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupMonomorphism.isGroupHomomorphism
d_isGroupHomomorphism_1548 ::
  T_IsGroupMonomorphism_648 -> T_IsGroupHomomorphism_622
d_isGroupHomomorphism_1548 v0
  = coe d_isGroupHomomorphism_656 (coe v0)
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_1550 ::
  T_IsGroupMonomorphism_648 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_1550 v0
  = coe
      d_isMagmaHomomorphism_358
      (coe
         d_isMonoidHomomorphism_630
         (coe d_isGroupHomomorphism_656 (coe v0)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupMonomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_1552 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupMonomorphism_648 -> T_IsMagmaMonomorphism_194
d_isMagmaMonomorphism_1552 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_1552 v7
du_isMagmaMonomorphism_1552 ::
  T_IsGroupMonomorphism_648 -> T_IsMagmaMonomorphism_194
du_isMagmaMonomorphism_1552 v0
  = coe
      du_isMagmaMonomorphism_396
      (coe du_isMonoidMonomorphism_676 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupMonomorphism.isMonoidHomomorphism
d_isMonoidHomomorphism_1554 ::
  T_IsGroupMonomorphism_648 -> T_IsMonoidHomomorphism_350
d_isMonoidHomomorphism_1554 v0
  = coe
      d_isMonoidHomomorphism_630 (coe d_isGroupHomomorphism_656 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupMonomorphism.isMonoidMonomorphism
d_isMonoidMonomorphism_1556 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupMonomorphism_648 -> T_IsMonoidMonomorphism_372
d_isMonoidMonomorphism_1556 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isMonoidMonomorphism_1556
du_isMonoidMonomorphism_1556 ::
  (AgdaAny -> AgdaAny) ->
  T_IsGroupMonomorphism_648 -> T_IsMonoidMonomorphism_372
du_isMonoidMonomorphism_1556 v0 v1
  = coe du_isMonoidMonomorphism_676 v1
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupMonomorphism.isRelHomomorphism
d_isRelHomomorphism_1558 ::
  T_IsGroupMonomorphism_648 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1558 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_isMonoidHomomorphism_630
            (coe d_isGroupHomomorphism_656 (coe v0))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupMonomorphism.isRelMonomorphism
d_isRelMonomorphism_1560 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupMonomorphism_648 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_1560 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_1560 v7
du_isRelMonomorphism_1560 ::
  T_IsGroupMonomorphism_648 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_1560 v0
  = let v1 = coe du_isMonoidMonomorphism_676 (coe v0) in
    coe
      (coe
         du_isRelMonomorphism_214 (coe du_isMagmaMonomorphism_396 (coe v1)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupMonomorphism.ε-homo
d_ε'45'homo_1562 :: T_IsGroupMonomorphism_648 -> AgdaAny
d_ε'45'homo_1562 v0
  = coe
      d_ε'45'homo_360
      (coe
         d_isMonoidHomomorphism_630
         (coe d_isGroupHomomorphism_656 (coe v0)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupMonomorphism.⁻¹-homo
d_'8315''185''45'homo_1564 ::
  T_IsGroupMonomorphism_648 -> AgdaAny -> AgdaAny
d_'8315''185''45'homo_1564 v0
  = coe
      d_'8315''185''45'homo_632 (coe d_isGroupHomomorphism_656 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupMonomorphism.homo
d_homo_1566 ::
  T_IsGroupMonomorphism_648 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1566 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_isMonoidHomomorphism_630
            (coe d_isGroupHomomorphism_656 (coe v0))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupMonomorphism.cong
d_cong_1568 ::
  T_IsGroupMonomorphism_648 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1568 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe
               d_isMonoidHomomorphism_630
               (coe d_isGroupHomomorphism_656 (coe v0)))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaHomomorphism
d_IsMagmaHomomorphism_1572 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaIsomorphism
d_IsMagmaIsomorphism_1574 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaMonomorphism
d_IsMagmaMonomorphism_1576 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaHomomorphism.homo
d_homo_1580 ::
  T_IsMagmaHomomorphism_176 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1580 v0 = coe d_homo_186 (coe v0)
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaHomomorphism.isRelHomomorphism
d_isRelHomomorphism_1582 ::
  T_IsMagmaHomomorphism_176 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1582 v0 = coe d_isRelHomomorphism_184 (coe v0)
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaHomomorphism.cong
d_cong_1584 ::
  T_IsMagmaHomomorphism_176 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1584 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe d_isRelHomomorphism_184 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaIsomorphism.homo
d_homo_1588 ::
  T_IsMagmaIsomorphism_218 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1588 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_202 (coe d_isMagmaMonomorphism_226 (coe v0)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaIsomorphism.injective
d_injective_1590 ::
  T_IsMagmaIsomorphism_218 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_1590 v0
  = coe d_injective_204 (coe d_isMagmaMonomorphism_226 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaIsomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_1592 ::
  T_IsMagmaIsomorphism_218 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_1592 v0
  = coe
      d_isMagmaHomomorphism_202 (coe d_isMagmaMonomorphism_226 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaIsomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_1594 ::
  T_IsMagmaIsomorphism_218 -> T_IsMagmaMonomorphism_194
d_isMagmaMonomorphism_1594 v0
  = coe d_isMagmaMonomorphism_226 (coe v0)
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaIsomorphism.isRelHomomorphism
d_isRelHomomorphism_1596 ::
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1596 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_202 (coe d_isMagmaMonomorphism_226 (coe v0)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaIsomorphism.isRelIsomorphism
d_isRelIsomorphism_1598 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
d_isRelIsomorphism_1598 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isRelIsomorphism_1598
du_isRelIsomorphism_1598 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
du_isRelIsomorphism_1598 v0 v1 = coe du_isRelIsomorphism_244 v1
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaIsomorphism.isRelMonomorphism
d_isRelMonomorphism_1600 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_1600 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_1600 v7
du_isRelMonomorphism_1600 ::
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_1600 v0
  = coe
      du_isRelMonomorphism_214 (coe d_isMagmaMonomorphism_226 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaIsomorphism.surjective
d_surjective_1602 ::
  T_IsMagmaIsomorphism_218 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_1602 v0 = coe d_surjective_228 (coe v0)
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaIsomorphism.cong
d_cong_1604 ::
  T_IsMagmaIsomorphism_218 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1604 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_202
            (coe d_isMagmaMonomorphism_226 (coe v0))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaMonomorphism.homo
d_homo_1608 ::
  T_IsMagmaMonomorphism_194 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1608 v0
  = coe d_homo_186 (coe d_isMagmaHomomorphism_202 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaMonomorphism.injective
d_injective_1610 ::
  T_IsMagmaMonomorphism_194 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_1610 v0 = coe d_injective_204 (coe v0)
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_1612 ::
  T_IsMagmaMonomorphism_194 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_1612 v0
  = coe d_isMagmaHomomorphism_202 (coe v0)
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaMonomorphism.isRelHomomorphism
d_isRelHomomorphism_1614 ::
  T_IsMagmaMonomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1614 v0
  = coe
      d_isRelHomomorphism_184 (coe d_isMagmaHomomorphism_202 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaMonomorphism.isRelMonomorphism
d_isRelMonomorphism_1616 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_1616 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isRelMonomorphism_1616
du_isRelMonomorphism_1616 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_1616 v0 v1 = coe du_isRelMonomorphism_214 v1
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaMonomorphism.cong
d_cong_1618 ::
  T_IsMagmaMonomorphism_194 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1618 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184 (coe d_isMagmaHomomorphism_202 (coe v0)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms._.Homomorphic₂
d_Homomorphic'8322'_1626 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8322'_1626 = erased
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneHomomorphism
d_IsRingWithoutOneHomomorphism_1632 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsRingWithoutOneHomomorphism_1632
  = C_IsRingWithoutOneHomomorphism'46'constructor_33433 T_IsGroupHomomorphism_622
                                                        (AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneHomomorphism.+-isGroupHomomorphism
d_'43''45'isGroupHomomorphism_1640 ::
  T_IsRingWithoutOneHomomorphism_1632 -> T_IsGroupHomomorphism_622
d_'43''45'isGroupHomomorphism_1640 v0
  = case coe v0 of
      C_IsRingWithoutOneHomomorphism'46'constructor_33433 v1 v2 -> coe v1
      _                                                         -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneHomomorphism.*-homo
d_'42''45'homo_1642 ::
  T_IsRingWithoutOneHomomorphism_1632 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_1642 v0
  = case coe v0 of
      C_IsRingWithoutOneHomomorphism'46'constructor_33433 v1 v2 -> coe v2
      _                                                         -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneHomomorphism._.homo
d_homo_1646 ::
  T_IsRingWithoutOneHomomorphism_1632 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_homo_1646 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_isMonoidHomomorphism_630
            (coe d_'43''45'isGroupHomomorphism_1640 (coe v0))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneHomomorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_1648 ::
  T_IsRingWithoutOneHomomorphism_1632 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_1648 v0
  = coe
      d_isMagmaHomomorphism_358
      (coe
         d_isMonoidHomomorphism_630
         (coe d_'43''45'isGroupHomomorphism_1640 (coe v0)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneHomomorphism._.ε-homo
d_ε'45'homo_1650 :: T_IsRingWithoutOneHomomorphism_1632 -> AgdaAny
d_ε'45'homo_1650 v0
  = coe
      d_ε'45'homo_360
      (coe
         d_isMonoidHomomorphism_630
         (coe d_'43''45'isGroupHomomorphism_1640 (coe v0)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneHomomorphism._.isMonoidHomomorphism
d_isMonoidHomomorphism_1652 ::
  T_IsRingWithoutOneHomomorphism_1632 -> T_IsMonoidHomomorphism_350
d_isMonoidHomomorphism_1652 v0
  = coe
      d_isMonoidHomomorphism_630
      (coe d_'43''45'isGroupHomomorphism_1640 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneHomomorphism._.isRelHomomorphism
d_isRelHomomorphism_1654 ::
  T_IsRingWithoutOneHomomorphism_1632 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1654 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_isMonoidHomomorphism_630
            (coe d_'43''45'isGroupHomomorphism_1640 (coe v0))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneHomomorphism._.⁻¹-homo
d_'8315''185''45'homo_1656 ::
  T_IsRingWithoutOneHomomorphism_1632 -> AgdaAny -> AgdaAny
d_'8315''185''45'homo_1656 v0
  = coe
      d_'8315''185''45'homo_632
      (coe d_'43''45'isGroupHomomorphism_1640 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneHomomorphism._.cong
d_cong_1658 ::
  T_IsRingWithoutOneHomomorphism_1632 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1658 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe
               d_isMonoidHomomorphism_630
               (coe d_'43''45'isGroupHomomorphism_1640 (coe v0)))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneHomomorphism.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_1660 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneHomomorphism_1632 -> T_IsMagmaHomomorphism_176
d_'42''45'isMagmaHomomorphism_1660 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_1660 v7
du_'42''45'isMagmaHomomorphism_1660 ::
  T_IsRingWithoutOneHomomorphism_1632 -> T_IsMagmaHomomorphism_176
du_'42''45'isMagmaHomomorphism_1660 v0
  = coe
      C_IsMagmaHomomorphism'46'constructor_4629
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe
               d_isMonoidHomomorphism_630
               (coe d_'43''45'isGroupHomomorphism_1640 (coe v0)))))
      (coe d_'42''45'homo_1642 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneMonomorphism
d_IsRingWithoutOneMonomorphism_1664 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsRingWithoutOneMonomorphism_1664
  = C_IsRingWithoutOneMonomorphism'46'constructor_34691 T_IsRingWithoutOneHomomorphism_1632
                                                        (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneMonomorphism.isRingWithoutOneHomomorphism
d_isRingWithoutOneHomomorphism_1672 ::
  T_IsRingWithoutOneMonomorphism_1664 ->
  T_IsRingWithoutOneHomomorphism_1632
d_isRingWithoutOneHomomorphism_1672 v0
  = case coe v0 of
      C_IsRingWithoutOneMonomorphism'46'constructor_34691 v1 v2 -> coe v1
      _                                                         -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneMonomorphism.injective
d_injective_1674 ::
  T_IsRingWithoutOneMonomorphism_1664 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_1674 v0
  = case coe v0 of
      C_IsRingWithoutOneMonomorphism'46'constructor_34691 v1 v2 -> coe v2
      _                                                         -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneMonomorphism._.*-homo
d_'42''45'homo_1678 ::
  T_IsRingWithoutOneMonomorphism_1664 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_1678 v0
  = coe
      d_'42''45'homo_1642
      (coe d_isRingWithoutOneHomomorphism_1672 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneMonomorphism._.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_1680 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneMonomorphism_1664 -> T_IsMagmaHomomorphism_176
d_'42''45'isMagmaHomomorphism_1680 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_1680 v7
du_'42''45'isMagmaHomomorphism_1680 ::
  T_IsRingWithoutOneMonomorphism_1664 -> T_IsMagmaHomomorphism_176
du_'42''45'isMagmaHomomorphism_1680 v0
  = coe
      du_'42''45'isMagmaHomomorphism_1660
      (coe d_isRingWithoutOneHomomorphism_1672 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneMonomorphism._.homo
d_homo_1682 ::
  T_IsRingWithoutOneMonomorphism_1664 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_homo_1682 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_isMonoidHomomorphism_630
            (coe
               d_'43''45'isGroupHomomorphism_1640
               (coe d_isRingWithoutOneHomomorphism_1672 (coe v0)))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneMonomorphism._.+-isGroupHomomorphism
d_'43''45'isGroupHomomorphism_1684 ::
  T_IsRingWithoutOneMonomorphism_1664 -> T_IsGroupHomomorphism_622
d_'43''45'isGroupHomomorphism_1684 v0
  = coe
      d_'43''45'isGroupHomomorphism_1640
      (coe d_isRingWithoutOneHomomorphism_1672 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneMonomorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_1686 ::
  T_IsRingWithoutOneMonomorphism_1664 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_1686 v0
  = coe
      d_isMagmaHomomorphism_358
      (coe
         d_isMonoidHomomorphism_630
         (coe
            d_'43''45'isGroupHomomorphism_1640
            (coe d_isRingWithoutOneHomomorphism_1672 (coe v0))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneMonomorphism._.ε-homo
d_ε'45'homo_1688 :: T_IsRingWithoutOneMonomorphism_1664 -> AgdaAny
d_ε'45'homo_1688 v0
  = coe
      d_ε'45'homo_360
      (coe
         d_isMonoidHomomorphism_630
         (coe
            d_'43''45'isGroupHomomorphism_1640
            (coe d_isRingWithoutOneHomomorphism_1672 (coe v0))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneMonomorphism._.isMonoidHomomorphism
d_isMonoidHomomorphism_1690 ::
  T_IsRingWithoutOneMonomorphism_1664 -> T_IsMonoidHomomorphism_350
d_isMonoidHomomorphism_1690 v0
  = coe
      d_isMonoidHomomorphism_630
      (coe
         d_'43''45'isGroupHomomorphism_1640
         (coe d_isRingWithoutOneHomomorphism_1672 (coe v0)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneMonomorphism._.isRelHomomorphism
d_isRelHomomorphism_1692 ::
  T_IsRingWithoutOneMonomorphism_1664 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1692 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_isMonoidHomomorphism_630
            (coe
               d_'43''45'isGroupHomomorphism_1640
               (coe d_isRingWithoutOneHomomorphism_1672 (coe v0)))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneMonomorphism._.⁻¹-homo
d_'8315''185''45'homo_1694 ::
  T_IsRingWithoutOneMonomorphism_1664 -> AgdaAny -> AgdaAny
d_'8315''185''45'homo_1694 v0
  = coe
      d_'8315''185''45'homo_632
      (coe
         d_'43''45'isGroupHomomorphism_1640
         (coe d_isRingWithoutOneHomomorphism_1672 (coe v0)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneMonomorphism._.cong
d_cong_1696 ::
  T_IsRingWithoutOneMonomorphism_1664 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1696 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe
               d_isMonoidHomomorphism_630
               (coe
                  d_'43''45'isGroupHomomorphism_1640
                  (coe d_isRingWithoutOneHomomorphism_1672 (coe v0))))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneMonomorphism.+-isGroupMonomorphism
d_'43''45'isGroupMonomorphism_1698 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneMonomorphism_1664 -> T_IsGroupMonomorphism_648
d_'43''45'isGroupMonomorphism_1698 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isGroupMonomorphism_1698 v7
du_'43''45'isGroupMonomorphism_1698 ::
  T_IsRingWithoutOneMonomorphism_1664 -> T_IsGroupMonomorphism_648
du_'43''45'isGroupMonomorphism_1698 v0
  = coe
      C_IsGroupMonomorphism'46'constructor_15537
      (coe
         d_'43''45'isGroupHomomorphism_1640
         (coe d_isRingWithoutOneHomomorphism_1672 (coe v0)))
      (coe d_injective_1674 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneMonomorphism._.isMagmaMonomorphism
d_isMagmaMonomorphism_1702 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneMonomorphism_1664 -> T_IsMagmaMonomorphism_194
d_isMagmaMonomorphism_1702 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_1702 v7
du_isMagmaMonomorphism_1702 ::
  T_IsRingWithoutOneMonomorphism_1664 -> T_IsMagmaMonomorphism_194
du_isMagmaMonomorphism_1702 v0
  = let v1 = coe du_'43''45'isGroupMonomorphism_1698 (coe v0) in
    coe
      (coe
         du_isMagmaMonomorphism_396
         (coe du_isMonoidMonomorphism_676 (coe v1)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneMonomorphism._.isMonoidMonomorphism
d_isMonoidMonomorphism_1704 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneMonomorphism_1664 -> T_IsMonoidMonomorphism_372
d_isMonoidMonomorphism_1704 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMonoidMonomorphism_1704 v7
du_isMonoidMonomorphism_1704 ::
  T_IsRingWithoutOneMonomorphism_1664 -> T_IsMonoidMonomorphism_372
du_isMonoidMonomorphism_1704 v0
  = coe
      du_isMonoidMonomorphism_676
      (coe du_'43''45'isGroupMonomorphism_1698 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneMonomorphism._.isRelMonomorphism
d_isRelMonomorphism_1706 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneMonomorphism_1664 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_1706 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_1706 v7
du_isRelMonomorphism_1706 ::
  T_IsRingWithoutOneMonomorphism_1664 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_1706 v0
  = let v1 = coe du_'43''45'isGroupMonomorphism_1698 (coe v0) in
    coe
      (let v2 = coe du_isMonoidMonomorphism_676 (coe v1) in
       coe
         (coe
            du_isRelMonomorphism_214
            (coe du_isMagmaMonomorphism_396 (coe v2))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneMonomorphism.*-isMagmaMonomorphism
d_'42''45'isMagmaMonomorphism_1708 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneMonomorphism_1664 -> T_IsMagmaMonomorphism_194
d_'42''45'isMagmaMonomorphism_1708 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaMonomorphism_1708 v7
du_'42''45'isMagmaMonomorphism_1708 ::
  T_IsRingWithoutOneMonomorphism_1664 -> T_IsMagmaMonomorphism_194
du_'42''45'isMagmaMonomorphism_1708 v0
  = coe
      C_IsMagmaMonomorphism'46'constructor_5763
      (coe
         du_'42''45'isMagmaHomomorphism_1660
         (coe d_isRingWithoutOneHomomorphism_1672 (coe v0)))
      (coe d_injective_1674 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism
d_IsRingWithoutOneIsoMorphism_1712 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsRingWithoutOneIsoMorphism_1712
  = C_IsRingWithoutOneIsoMorphism'46'constructor_36755 T_IsRingWithoutOneMonomorphism_1664
                                                       (AgdaAny ->
                                                        MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism.isRingWithoutOneMonomorphism
d_isRingWithoutOneMonomorphism_1720 ::
  T_IsRingWithoutOneIsoMorphism_1712 ->
  T_IsRingWithoutOneMonomorphism_1664
d_isRingWithoutOneMonomorphism_1720 v0
  = case coe v0 of
      C_IsRingWithoutOneIsoMorphism'46'constructor_36755 v1 v2 -> coe v1
      _                                                        -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism.surjective
d_surjective_1722 ::
  T_IsRingWithoutOneIsoMorphism_1712 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_1722 v0
  = case coe v0 of
      C_IsRingWithoutOneIsoMorphism'46'constructor_36755 v1 v2 -> coe v2
      _                                                        -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.*-homo
d_'42''45'homo_1726 ::
  T_IsRingWithoutOneIsoMorphism_1712 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_1726 v0
  = coe
      d_'42''45'homo_1642
      (coe
         d_isRingWithoutOneHomomorphism_1672
         (coe d_isRingWithoutOneMonomorphism_1720 (coe v0)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_1728 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneIsoMorphism_1712 -> T_IsMagmaHomomorphism_176
d_'42''45'isMagmaHomomorphism_1728 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_1728 v7
du_'42''45'isMagmaHomomorphism_1728 ::
  T_IsRingWithoutOneIsoMorphism_1712 -> T_IsMagmaHomomorphism_176
du_'42''45'isMagmaHomomorphism_1728 v0
  = let v1 = d_isRingWithoutOneMonomorphism_1720 (coe v0) in
    coe
      (coe
         du_'42''45'isMagmaHomomorphism_1660
         (coe d_isRingWithoutOneHomomorphism_1672 (coe v1)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.*-isMagmaMonomorphism
d_'42''45'isMagmaMonomorphism_1730 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneIsoMorphism_1712 -> T_IsMagmaMonomorphism_194
d_'42''45'isMagmaMonomorphism_1730 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaMonomorphism_1730 v7
du_'42''45'isMagmaMonomorphism_1730 ::
  T_IsRingWithoutOneIsoMorphism_1712 -> T_IsMagmaMonomorphism_194
du_'42''45'isMagmaMonomorphism_1730 v0
  = coe
      du_'42''45'isMagmaMonomorphism_1708
      (coe d_isRingWithoutOneMonomorphism_1720 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.homo
d_homo_1732 ::
  T_IsRingWithoutOneIsoMorphism_1712 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1732 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_isMonoidHomomorphism_630
            (coe
               d_'43''45'isGroupHomomorphism_1640
               (coe
                  d_isRingWithoutOneHomomorphism_1672
                  (coe d_isRingWithoutOneMonomorphism_1720 (coe v0))))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.+-isGroupHomomorphism
d_'43''45'isGroupHomomorphism_1734 ::
  T_IsRingWithoutOneIsoMorphism_1712 -> T_IsGroupHomomorphism_622
d_'43''45'isGroupHomomorphism_1734 v0
  = coe
      d_'43''45'isGroupHomomorphism_1640
      (coe
         d_isRingWithoutOneHomomorphism_1672
         (coe d_isRingWithoutOneMonomorphism_1720 (coe v0)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.+-isGroupMonomorphism
d_'43''45'isGroupMonomorphism_1736 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneIsoMorphism_1712 -> T_IsGroupMonomorphism_648
d_'43''45'isGroupMonomorphism_1736 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isGroupMonomorphism_1736 v7
du_'43''45'isGroupMonomorphism_1736 ::
  T_IsRingWithoutOneIsoMorphism_1712 -> T_IsGroupMonomorphism_648
du_'43''45'isGroupMonomorphism_1736 v0
  = coe
      du_'43''45'isGroupMonomorphism_1698
      (coe d_isRingWithoutOneMonomorphism_1720 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_1738 ::
  T_IsRingWithoutOneIsoMorphism_1712 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_1738 v0
  = coe
      d_isMagmaHomomorphism_358
      (coe
         d_isMonoidHomomorphism_630
         (coe
            d_'43''45'isGroupHomomorphism_1640
            (coe
               d_isRingWithoutOneHomomorphism_1672
               (coe d_isRingWithoutOneMonomorphism_1720 (coe v0)))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.isMagmaMonomorphism
d_isMagmaMonomorphism_1740 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneIsoMorphism_1712 -> T_IsMagmaMonomorphism_194
d_isMagmaMonomorphism_1740 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_1740 v7
du_isMagmaMonomorphism_1740 ::
  T_IsRingWithoutOneIsoMorphism_1712 -> T_IsMagmaMonomorphism_194
du_isMagmaMonomorphism_1740 v0
  = let v1 = d_isRingWithoutOneMonomorphism_1720 (coe v0) in
    coe
      (let v2 = coe du_'43''45'isGroupMonomorphism_1698 (coe v1) in
       coe
         (coe
            du_isMagmaMonomorphism_396
            (coe du_isMonoidMonomorphism_676 (coe v2))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.isMonoidMonomorphism
d_isMonoidMonomorphism_1742 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneIsoMorphism_1712 -> T_IsMonoidMonomorphism_372
d_isMonoidMonomorphism_1742 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMonoidMonomorphism_1742 v7
du_isMonoidMonomorphism_1742 ::
  T_IsRingWithoutOneIsoMorphism_1712 -> T_IsMonoidMonomorphism_372
du_isMonoidMonomorphism_1742 v0
  = let v1 = d_isRingWithoutOneMonomorphism_1720 (coe v0) in
    coe
      (coe
         du_isMonoidMonomorphism_676
         (coe du_'43''45'isGroupMonomorphism_1698 (coe v1)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.ε-homo
d_ε'45'homo_1744 :: T_IsRingWithoutOneIsoMorphism_1712 -> AgdaAny
d_ε'45'homo_1744 v0
  = coe
      d_ε'45'homo_360
      (coe
         d_isMonoidHomomorphism_630
         (coe
            d_'43''45'isGroupHomomorphism_1640
            (coe
               d_isRingWithoutOneHomomorphism_1672
               (coe d_isRingWithoutOneMonomorphism_1720 (coe v0)))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.injective
d_injective_1746 ::
  T_IsRingWithoutOneIsoMorphism_1712 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_1746 v0
  = coe
      d_injective_1674 (coe d_isRingWithoutOneMonomorphism_1720 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.isMonoidHomomorphism
d_isMonoidHomomorphism_1748 ::
  T_IsRingWithoutOneIsoMorphism_1712 -> T_IsMonoidHomomorphism_350
d_isMonoidHomomorphism_1748 v0
  = coe
      d_isMonoidHomomorphism_630
      (coe
         d_'43''45'isGroupHomomorphism_1640
         (coe
            d_isRingWithoutOneHomomorphism_1672
            (coe d_isRingWithoutOneMonomorphism_1720 (coe v0))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.isRelHomomorphism
d_isRelHomomorphism_1750 ::
  T_IsRingWithoutOneIsoMorphism_1712 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1750 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_isMonoidHomomorphism_630
            (coe
               d_'43''45'isGroupHomomorphism_1640
               (coe
                  d_isRingWithoutOneHomomorphism_1672
                  (coe d_isRingWithoutOneMonomorphism_1720 (coe v0))))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.isRelMonomorphism
d_isRelMonomorphism_1752 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneIsoMorphism_1712 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_1752 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_1752 v7
du_isRelMonomorphism_1752 ::
  T_IsRingWithoutOneIsoMorphism_1712 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_1752 v0
  = let v1 = d_isRingWithoutOneMonomorphism_1720 (coe v0) in
    coe
      (let v2 = coe du_'43''45'isGroupMonomorphism_1698 (coe v1) in
       coe
         (let v3 = coe du_isMonoidMonomorphism_676 (coe v2) in
          coe
            (coe
               du_isRelMonomorphism_214
               (coe du_isMagmaMonomorphism_396 (coe v3)))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.isRingWithoutOneHomomorphism
d_isRingWithoutOneHomomorphism_1754 ::
  T_IsRingWithoutOneIsoMorphism_1712 ->
  T_IsRingWithoutOneHomomorphism_1632
d_isRingWithoutOneHomomorphism_1754 v0
  = coe
      d_isRingWithoutOneHomomorphism_1672
      (coe d_isRingWithoutOneMonomorphism_1720 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.⁻¹-homo
d_'8315''185''45'homo_1756 ::
  T_IsRingWithoutOneIsoMorphism_1712 -> AgdaAny -> AgdaAny
d_'8315''185''45'homo_1756 v0
  = coe
      d_'8315''185''45'homo_632
      (coe
         d_'43''45'isGroupHomomorphism_1640
         (coe
            d_isRingWithoutOneHomomorphism_1672
            (coe d_isRingWithoutOneMonomorphism_1720 (coe v0))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.cong
d_cong_1758 ::
  T_IsRingWithoutOneIsoMorphism_1712 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1758 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe
               d_isMonoidHomomorphism_630
               (coe
                  d_'43''45'isGroupHomomorphism_1640
                  (coe
                     d_isRingWithoutOneHomomorphism_1672
                     (coe d_isRingWithoutOneMonomorphism_1720 (coe v0)))))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism.+-isGroupIsomorphism
d_'43''45'isGroupIsomorphism_1760 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneIsoMorphism_1712 -> T_IsGroupIsomorphism_686
d_'43''45'isGroupIsomorphism_1760 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isGroupIsomorphism_1760 v7
du_'43''45'isGroupIsomorphism_1760 ::
  T_IsRingWithoutOneIsoMorphism_1712 -> T_IsGroupIsomorphism_686
du_'43''45'isGroupIsomorphism_1760 v0
  = coe
      C_IsGroupIsomorphism'46'constructor_17073
      (coe
         du_'43''45'isGroupMonomorphism_1698
         (coe d_isRingWithoutOneMonomorphism_1720 (coe v0)))
      (coe d_surjective_1722 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.isMagmaIsomorphism
d_isMagmaIsomorphism_1764 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneIsoMorphism_1712 -> T_IsMagmaIsomorphism_218
d_isMagmaIsomorphism_1764 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaIsomorphism_1764 v7
du_isMagmaIsomorphism_1764 ::
  T_IsRingWithoutOneIsoMorphism_1712 -> T_IsMagmaIsomorphism_218
du_isMagmaIsomorphism_1764 v0
  = let v1 = coe du_'43''45'isGroupIsomorphism_1760 (coe v0) in
    coe
      (coe
         du_isMagmaIsomorphism_436
         (coe du_isMonoidIsomorphism_724 (coe v1)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.isMonoidIsomorphism
d_isMonoidIsomorphism_1766 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneIsoMorphism_1712 -> T_IsMonoidIsomorphism_404
d_isMonoidIsomorphism_1766 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMonoidIsomorphism_1766 v7
du_isMonoidIsomorphism_1766 ::
  T_IsRingWithoutOneIsoMorphism_1712 -> T_IsMonoidIsomorphism_404
du_isMonoidIsomorphism_1766 v0
  = coe
      du_isMonoidIsomorphism_724
      (coe du_'43''45'isGroupIsomorphism_1760 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.isRelIsomorphism
d_isRelIsomorphism_1768 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneIsoMorphism_1712 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
d_isRelIsomorphism_1768 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelIsomorphism_1768 v7
du_isRelIsomorphism_1768 ::
  T_IsRingWithoutOneIsoMorphism_1712 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
du_isRelIsomorphism_1768 v0
  = let v1 = coe du_'43''45'isGroupIsomorphism_1760 (coe v0) in
    coe
      (let v2 = coe du_isMonoidIsomorphism_724 (coe v1) in
       coe
         (coe
            du_isRelIsomorphism_244 (coe du_isMagmaIsomorphism_436 (coe v2))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism.*-isMagmaIsomorphism
d_'42''45'isMagmaIsomorphism_1770 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_222 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneIsoMorphism_1712 -> T_IsMagmaIsomorphism_218
d_'42''45'isMagmaIsomorphism_1770 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaIsomorphism_1770 v7
du_'42''45'isMagmaIsomorphism_1770 ::
  T_IsRingWithoutOneIsoMorphism_1712 -> T_IsMagmaIsomorphism_218
du_'42''45'isMagmaIsomorphism_1770 v0
  = coe
      C_IsMagmaIsomorphism'46'constructor_7199
      (coe
         du_'42''45'isMagmaMonomorphism_1708
         (coe d_isRingWithoutOneMonomorphism_1720 (coe v0)))
      (coe d_surjective_1722 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms._._≈_
d__'8776'__1792 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__1792 = erased
-- Algebra.Morphism.Structures.RingMorphisms._.-_
d_'45'__1806 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  AgdaAny -> AgdaAny
d_'45'__1806 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_'45'__1806 v4
du_'45'__1806 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  AgdaAny -> AgdaAny
du_'45'__1806 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__296 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms._.Carrier
d_Carrier_1812 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 -> ()
d_Carrier_1812 = erased
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupHomomorphism
d_IsGroupHomomorphism_1852 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupIsomorphism
d_IsGroupIsomorphism_1854 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupMonomorphism
d_IsGroupMonomorphism_1856 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupHomomorphism.homo
d_homo_1860 ::
  T_IsGroupHomomorphism_622 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1860 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe d_isMonoidHomomorphism_630 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupHomomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_1862 ::
  T_IsGroupHomomorphism_622 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_1862 v0
  = coe
      d_isMagmaHomomorphism_358 (coe d_isMonoidHomomorphism_630 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupHomomorphism.isMonoidHomomorphism
d_isMonoidHomomorphism_1864 ::
  T_IsGroupHomomorphism_622 -> T_IsMonoidHomomorphism_350
d_isMonoidHomomorphism_1864 v0
  = coe d_isMonoidHomomorphism_630 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupHomomorphism.isRelHomomorphism
d_isRelHomomorphism_1866 ::
  T_IsGroupHomomorphism_622 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1866 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe d_isMonoidHomomorphism_630 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupHomomorphism.ε-homo
d_ε'45'homo_1868 :: T_IsGroupHomomorphism_622 -> AgdaAny
d_ε'45'homo_1868 v0
  = coe d_ε'45'homo_360 (coe d_isMonoidHomomorphism_630 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupHomomorphism.⁻¹-homo
d_'8315''185''45'homo_1870 ::
  T_IsGroupHomomorphism_622 -> AgdaAny -> AgdaAny
d_'8315''185''45'homo_1870 v0
  = coe d_'8315''185''45'homo_632 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupHomomorphism.cong
d_cong_1872 ::
  T_IsGroupHomomorphism_622 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1872 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe d_isMonoidHomomorphism_630 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupIsomorphism.injective
d_injective_1876 ::
  T_IsGroupIsomorphism_686 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_1876 v0
  = coe d_injective_658 (coe d_isGroupMonomorphism_694 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupIsomorphism.isGroupHomomorphism
d_isGroupHomomorphism_1878 ::
  T_IsGroupIsomorphism_686 -> T_IsGroupHomomorphism_622
d_isGroupHomomorphism_1878 v0
  = coe
      d_isGroupHomomorphism_656 (coe d_isGroupMonomorphism_694 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupIsomorphism.isGroupMonomorphism
d_isGroupMonomorphism_1880 ::
  T_IsGroupIsomorphism_686 -> T_IsGroupMonomorphism_648
d_isGroupMonomorphism_1880 v0
  = coe d_isGroupMonomorphism_694 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupIsomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_1882 ::
  T_IsGroupIsomorphism_686 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_1882 v0
  = coe
      d_isMagmaHomomorphism_358
      (coe
         d_isMonoidHomomorphism_630
         (coe
            d_isGroupHomomorphism_656
            (coe d_isGroupMonomorphism_694 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupIsomorphism.isMagmaIsomorphism
d_isMagmaIsomorphism_1884 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupIsomorphism_686 -> T_IsMagmaIsomorphism_218
d_isMagmaIsomorphism_1884 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaIsomorphism_1884 v7
du_isMagmaIsomorphism_1884 ::
  T_IsGroupIsomorphism_686 -> T_IsMagmaIsomorphism_218
du_isMagmaIsomorphism_1884 v0
  = coe
      du_isMagmaIsomorphism_436 (coe du_isMonoidIsomorphism_724 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupIsomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_1886 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupIsomorphism_686 -> T_IsMagmaMonomorphism_194
d_isMagmaMonomorphism_1886 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_1886 v7
du_isMagmaMonomorphism_1886 ::
  T_IsGroupIsomorphism_686 -> T_IsMagmaMonomorphism_194
du_isMagmaMonomorphism_1886 v0
  = let v1 = d_isGroupMonomorphism_694 (coe v0) in
    coe
      (coe
         du_isMagmaMonomorphism_396
         (coe du_isMonoidMonomorphism_676 (coe v1)))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupIsomorphism.isMonoidHomomorphism
d_isMonoidHomomorphism_1888 ::
  T_IsGroupIsomorphism_686 -> T_IsMonoidHomomorphism_350
d_isMonoidHomomorphism_1888 v0
  = coe
      d_isMonoidHomomorphism_630
      (coe
         d_isGroupHomomorphism_656 (coe d_isGroupMonomorphism_694 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupIsomorphism.isMonoidIsomorphism
d_isMonoidIsomorphism_1890 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupIsomorphism_686 -> T_IsMonoidIsomorphism_404
d_isMonoidIsomorphism_1890 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isMonoidIsomorphism_1890
du_isMonoidIsomorphism_1890 ::
  (AgdaAny -> AgdaAny) ->
  T_IsGroupIsomorphism_686 -> T_IsMonoidIsomorphism_404
du_isMonoidIsomorphism_1890 v0 v1
  = coe du_isMonoidIsomorphism_724 v1
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupIsomorphism.isMonoidMonomorphism
d_isMonoidMonomorphism_1892 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupIsomorphism_686 -> T_IsMonoidMonomorphism_372
d_isMonoidMonomorphism_1892 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMonoidMonomorphism_1892 v7
du_isMonoidMonomorphism_1892 ::
  T_IsGroupIsomorphism_686 -> T_IsMonoidMonomorphism_372
du_isMonoidMonomorphism_1892 v0
  = coe
      du_isMonoidMonomorphism_676
      (coe d_isGroupMonomorphism_694 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupIsomorphism.isRelHomomorphism
d_isRelHomomorphism_1894 ::
  T_IsGroupIsomorphism_686 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1894 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_isMonoidHomomorphism_630
            (coe
               d_isGroupHomomorphism_656
               (coe d_isGroupMonomorphism_694 (coe v0)))))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupIsomorphism.isRelIsomorphism
d_isRelIsomorphism_1896 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupIsomorphism_686 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
d_isRelIsomorphism_1896 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelIsomorphism_1896 v7
du_isRelIsomorphism_1896 ::
  T_IsGroupIsomorphism_686 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
du_isRelIsomorphism_1896 v0
  = let v1 = coe du_isMonoidIsomorphism_724 (coe v0) in
    coe
      (coe
         du_isRelIsomorphism_244 (coe du_isMagmaIsomorphism_436 (coe v1)))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupIsomorphism.isRelMonomorphism
d_isRelMonomorphism_1898 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupIsomorphism_686 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_1898 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_1898 v7
du_isRelMonomorphism_1898 ::
  T_IsGroupIsomorphism_686 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_1898 v0
  = let v1 = d_isGroupMonomorphism_694 (coe v0) in
    coe
      (let v2 = coe du_isMonoidMonomorphism_676 (coe v1) in
       coe
         (coe
            du_isRelMonomorphism_214
            (coe du_isMagmaMonomorphism_396 (coe v2))))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupIsomorphism.surjective
d_surjective_1900 ::
  T_IsGroupIsomorphism_686 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_1900 v0 = coe d_surjective_696 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupIsomorphism.ε-homo
d_ε'45'homo_1902 :: T_IsGroupIsomorphism_686 -> AgdaAny
d_ε'45'homo_1902 v0
  = coe
      d_ε'45'homo_360
      (coe
         d_isMonoidHomomorphism_630
         (coe
            d_isGroupHomomorphism_656
            (coe d_isGroupMonomorphism_694 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupIsomorphism.⁻¹-homo
d_'8315''185''45'homo_1904 ::
  T_IsGroupIsomorphism_686 -> AgdaAny -> AgdaAny
d_'8315''185''45'homo_1904 v0
  = coe
      d_'8315''185''45'homo_632
      (coe
         d_isGroupHomomorphism_656 (coe d_isGroupMonomorphism_694 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupIsomorphism.homo
d_homo_1906 ::
  T_IsGroupIsomorphism_686 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1906 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_isMonoidHomomorphism_630
            (coe
               d_isGroupHomomorphism_656
               (coe d_isGroupMonomorphism_694 (coe v0)))))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupIsomorphism.cong
d_cong_1908 ::
  T_IsGroupIsomorphism_686 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1908 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe
               d_isMonoidHomomorphism_630
               (coe
                  d_isGroupHomomorphism_656
                  (coe d_isGroupMonomorphism_694 (coe v0))))))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupMonomorphism.injective
d_injective_1912 ::
  T_IsGroupMonomorphism_648 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_1912 v0 = coe d_injective_658 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupMonomorphism.isGroupHomomorphism
d_isGroupHomomorphism_1914 ::
  T_IsGroupMonomorphism_648 -> T_IsGroupHomomorphism_622
d_isGroupHomomorphism_1914 v0
  = coe d_isGroupHomomorphism_656 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_1916 ::
  T_IsGroupMonomorphism_648 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_1916 v0
  = coe
      d_isMagmaHomomorphism_358
      (coe
         d_isMonoidHomomorphism_630
         (coe d_isGroupHomomorphism_656 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupMonomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_1918 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupMonomorphism_648 -> T_IsMagmaMonomorphism_194
d_isMagmaMonomorphism_1918 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_1918 v7
du_isMagmaMonomorphism_1918 ::
  T_IsGroupMonomorphism_648 -> T_IsMagmaMonomorphism_194
du_isMagmaMonomorphism_1918 v0
  = coe
      du_isMagmaMonomorphism_396
      (coe du_isMonoidMonomorphism_676 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupMonomorphism.isMonoidHomomorphism
d_isMonoidHomomorphism_1920 ::
  T_IsGroupMonomorphism_648 -> T_IsMonoidHomomorphism_350
d_isMonoidHomomorphism_1920 v0
  = coe
      d_isMonoidHomomorphism_630 (coe d_isGroupHomomorphism_656 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupMonomorphism.isMonoidMonomorphism
d_isMonoidMonomorphism_1922 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupMonomorphism_648 -> T_IsMonoidMonomorphism_372
d_isMonoidMonomorphism_1922 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isMonoidMonomorphism_1922
du_isMonoidMonomorphism_1922 ::
  (AgdaAny -> AgdaAny) ->
  T_IsGroupMonomorphism_648 -> T_IsMonoidMonomorphism_372
du_isMonoidMonomorphism_1922 v0 v1
  = coe du_isMonoidMonomorphism_676 v1
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupMonomorphism.isRelHomomorphism
d_isRelHomomorphism_1924 ::
  T_IsGroupMonomorphism_648 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1924 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_isMonoidHomomorphism_630
            (coe d_isGroupHomomorphism_656 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupMonomorphism.isRelMonomorphism
d_isRelMonomorphism_1926 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupMonomorphism_648 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_1926 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_1926 v7
du_isRelMonomorphism_1926 ::
  T_IsGroupMonomorphism_648 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_1926 v0
  = let v1 = coe du_isMonoidMonomorphism_676 (coe v0) in
    coe
      (coe
         du_isRelMonomorphism_214 (coe du_isMagmaMonomorphism_396 (coe v1)))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupMonomorphism.ε-homo
d_ε'45'homo_1928 :: T_IsGroupMonomorphism_648 -> AgdaAny
d_ε'45'homo_1928 v0
  = coe
      d_ε'45'homo_360
      (coe
         d_isMonoidHomomorphism_630
         (coe d_isGroupHomomorphism_656 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupMonomorphism.⁻¹-homo
d_'8315''185''45'homo_1930 ::
  T_IsGroupMonomorphism_648 -> AgdaAny -> AgdaAny
d_'8315''185''45'homo_1930 v0
  = coe
      d_'8315''185''45'homo_632 (coe d_isGroupHomomorphism_656 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupMonomorphism.homo
d_homo_1932 ::
  T_IsGroupMonomorphism_648 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1932 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_isMonoidHomomorphism_630
            (coe d_isGroupHomomorphism_656 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupMonomorphism.cong
d_cong_1934 ::
  T_IsGroupMonomorphism_648 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1934 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe
               d_isMonoidHomomorphism_630
               (coe d_isGroupHomomorphism_656 (coe v0)))))
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidHomomorphism
d_IsMonoidHomomorphism_1938 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidIsomorphism
d_IsMonoidIsomorphism_1940 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidMonomorphism
d_IsMonoidMonomorphism_1942 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidHomomorphism.homo
d_homo_1946 ::
  T_IsMonoidHomomorphism_350 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1946 v0
  = coe d_homo_186 (coe d_isMagmaHomomorphism_358 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidHomomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_1948 ::
  T_IsMonoidHomomorphism_350 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_1948 v0
  = coe d_isMagmaHomomorphism_358 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidHomomorphism.isRelHomomorphism
d_isRelHomomorphism_1950 ::
  T_IsMonoidHomomorphism_350 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1950 v0
  = coe
      d_isRelHomomorphism_184 (coe d_isMagmaHomomorphism_358 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidHomomorphism.ε-homo
d_ε'45'homo_1952 :: T_IsMonoidHomomorphism_350 -> AgdaAny
d_ε'45'homo_1952 v0 = coe d_ε'45'homo_360 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidHomomorphism.cong
d_cong_1954 ::
  T_IsMonoidHomomorphism_350 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1954 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184 (coe d_isMagmaHomomorphism_358 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidIsomorphism.homo
d_homo_1958 ::
  T_IsMonoidIsomorphism_404 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1958 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_isMonoidHomomorphism_380
            (coe d_isMonoidMonomorphism_412 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidIsomorphism.injective
d_injective_1960 ::
  T_IsMonoidIsomorphism_404 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_1960 v0
  = coe d_injective_382 (coe d_isMonoidMonomorphism_412 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidIsomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_1962 ::
  T_IsMonoidIsomorphism_404 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_1962 v0
  = coe
      d_isMagmaHomomorphism_358
      (coe
         d_isMonoidHomomorphism_380
         (coe d_isMonoidMonomorphism_412 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidIsomorphism.isMagmaIsomorphism
d_isMagmaIsomorphism_1964 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_404 -> T_IsMagmaIsomorphism_218
d_isMagmaIsomorphism_1964 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isMagmaIsomorphism_1964
du_isMagmaIsomorphism_1964 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_404 -> T_IsMagmaIsomorphism_218
du_isMagmaIsomorphism_1964 v0 v1 = coe du_isMagmaIsomorphism_436 v1
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidIsomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_1966 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_404 -> T_IsMagmaMonomorphism_194
d_isMagmaMonomorphism_1966 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_1966 v7
du_isMagmaMonomorphism_1966 ::
  T_IsMonoidIsomorphism_404 -> T_IsMagmaMonomorphism_194
du_isMagmaMonomorphism_1966 v0
  = coe
      du_isMagmaMonomorphism_396
      (coe d_isMonoidMonomorphism_412 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidIsomorphism.isMonoidHomomorphism
d_isMonoidHomomorphism_1968 ::
  T_IsMonoidIsomorphism_404 -> T_IsMonoidHomomorphism_350
d_isMonoidHomomorphism_1968 v0
  = coe
      d_isMonoidHomomorphism_380
      (coe d_isMonoidMonomorphism_412 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidIsomorphism.isMonoidMonomorphism
d_isMonoidMonomorphism_1970 ::
  T_IsMonoidIsomorphism_404 -> T_IsMonoidMonomorphism_372
d_isMonoidMonomorphism_1970 v0
  = coe d_isMonoidMonomorphism_412 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidIsomorphism.isRelHomomorphism
d_isRelHomomorphism_1972 ::
  T_IsMonoidIsomorphism_404 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1972 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_isMonoidHomomorphism_380
            (coe d_isMonoidMonomorphism_412 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidIsomorphism.isRelIsomorphism
d_isRelIsomorphism_1974 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_404 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
d_isRelIsomorphism_1974 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelIsomorphism_1974 v7
du_isRelIsomorphism_1974 ::
  T_IsMonoidIsomorphism_404 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
du_isRelIsomorphism_1974 v0
  = coe
      du_isRelIsomorphism_244 (coe du_isMagmaIsomorphism_436 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidIsomorphism.isRelMonomorphism
d_isRelMonomorphism_1976 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_404 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_1976 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_1976 v7
du_isRelMonomorphism_1976 ::
  T_IsMonoidIsomorphism_404 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_1976 v0
  = let v1 = d_isMonoidMonomorphism_412 (coe v0) in
    coe
      (coe
         du_isRelMonomorphism_214 (coe du_isMagmaMonomorphism_396 (coe v1)))
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidIsomorphism.surjective
d_surjective_1978 ::
  T_IsMonoidIsomorphism_404 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_1978 v0 = coe d_surjective_414 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidIsomorphism.ε-homo
d_ε'45'homo_1980 :: T_IsMonoidIsomorphism_404 -> AgdaAny
d_ε'45'homo_1980 v0
  = coe
      d_ε'45'homo_360
      (coe
         d_isMonoidHomomorphism_380
         (coe d_isMonoidMonomorphism_412 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidIsomorphism.cong
d_cong_1982 ::
  T_IsMonoidIsomorphism_404 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1982 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe
               d_isMonoidHomomorphism_380
               (coe d_isMonoidMonomorphism_412 (coe v0)))))
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidMonomorphism.homo
d_homo_1986 ::
  T_IsMonoidMonomorphism_372 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1986 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe d_isMonoidHomomorphism_380 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidMonomorphism.injective
d_injective_1988 ::
  T_IsMonoidMonomorphism_372 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_1988 v0 = coe d_injective_382 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_1990 ::
  T_IsMonoidMonomorphism_372 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_1990 v0
  = coe
      d_isMagmaHomomorphism_358 (coe d_isMonoidHomomorphism_380 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidMonomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_1992 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidMonomorphism_372 -> T_IsMagmaMonomorphism_194
d_isMagmaMonomorphism_1992 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isMagmaMonomorphism_1992
du_isMagmaMonomorphism_1992 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidMonomorphism_372 -> T_IsMagmaMonomorphism_194
du_isMagmaMonomorphism_1992 v0 v1
  = coe du_isMagmaMonomorphism_396 v1
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidMonomorphism.isMonoidHomomorphism
d_isMonoidHomomorphism_1994 ::
  T_IsMonoidMonomorphism_372 -> T_IsMonoidHomomorphism_350
d_isMonoidHomomorphism_1994 v0
  = coe d_isMonoidHomomorphism_380 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidMonomorphism.isRelHomomorphism
d_isRelHomomorphism_1996 ::
  T_IsMonoidMonomorphism_372 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1996 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe d_isMonoidHomomorphism_380 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidMonomorphism.isRelMonomorphism
d_isRelMonomorphism_1998 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidMonomorphism_372 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_1998 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_1998 v7
du_isRelMonomorphism_1998 ::
  T_IsMonoidMonomorphism_372 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_1998 v0
  = coe
      du_isRelMonomorphism_214 (coe du_isMagmaMonomorphism_396 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidMonomorphism.ε-homo
d_ε'45'homo_2000 :: T_IsMonoidMonomorphism_372 -> AgdaAny
d_ε'45'homo_2000 v0
  = coe d_ε'45'homo_360 (coe d_isMonoidHomomorphism_380 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidMonomorphism.cong
d_cong_2002 ::
  T_IsMonoidMonomorphism_372 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2002 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe d_isMonoidHomomorphism_380 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms._.Homomorphic₁
d_Homomorphic'8321'_2008 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8321'_2008 = erased
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringHomomorphism
d_IsSemiringHomomorphism_2016 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism
d_IsSemiringIsomorphism_2018 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringMonomorphism
d_IsSemiringMonomorphism_2020 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringHomomorphism.*-homo
d_'42''45'homo_2024 ::
  T_IsSemiringHomomorphism_1282 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_2024 v0
  = coe
      d_'42''45'homo_926 (coe d_isNearSemiringHomomorphism_1290 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringHomomorphism.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_2026 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringHomomorphism_1282 -> T_IsMagmaHomomorphism_176
d_'42''45'isMagmaHomomorphism_2026 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_2026 v7
du_'42''45'isMagmaHomomorphism_2026 ::
  T_IsSemiringHomomorphism_1282 -> T_IsMagmaHomomorphism_176
du_'42''45'isMagmaHomomorphism_2026 v0
  = coe
      du_'42''45'isMagmaHomomorphism_940
      (coe d_isNearSemiringHomomorphism_1290 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringHomomorphism.*-isMonoidHomomorphism
d_'42''45'isMonoidHomomorphism_2028 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringHomomorphism_1282 -> T_IsMonoidHomomorphism_350
d_'42''45'isMonoidHomomorphism_2028 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'42''45'isMonoidHomomorphism_2028
du_'42''45'isMonoidHomomorphism_2028 ::
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringHomomorphism_1282 -> T_IsMonoidHomomorphism_350
du_'42''45'isMonoidHomomorphism_2028 v0 v1
  = coe du_'42''45'isMonoidHomomorphism_1312 v1
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringHomomorphism.homo
d_homo_2030 ::
  T_IsSemiringHomomorphism_1282 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2030 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_'43''45'isMonoidHomomorphism_924
            (coe d_isNearSemiringHomomorphism_1290 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringHomomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_2032 ::
  T_IsSemiringHomomorphism_1282 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_2032 v0
  = coe
      d_isMagmaHomomorphism_358
      (coe
         d_'43''45'isMonoidHomomorphism_924
         (coe d_isNearSemiringHomomorphism_1290 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringHomomorphism.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_2034 ::
  T_IsSemiringHomomorphism_1282 -> T_IsMonoidHomomorphism_350
d_'43''45'isMonoidHomomorphism_2034 v0
  = coe
      d_'43''45'isMonoidHomomorphism_924
      (coe d_isNearSemiringHomomorphism_1290 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringHomomorphism.ε-homo
d_ε'45'homo_2036 :: T_IsSemiringHomomorphism_1282 -> AgdaAny
d_ε'45'homo_2036 v0
  = coe
      d_ε'45'homo_360
      (coe
         d_'43''45'isMonoidHomomorphism_924
         (coe d_isNearSemiringHomomorphism_1290 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringHomomorphism.1#-homo
d_1'35''45'homo_2038 :: T_IsSemiringHomomorphism_1282 -> AgdaAny
d_1'35''45'homo_2038 v0 = coe d_1'35''45'homo_1292 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringHomomorphism.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_2040 ::
  T_IsSemiringHomomorphism_1282 -> T_IsNearSemiringHomomorphism_916
d_isNearSemiringHomomorphism_2040 v0
  = coe d_isNearSemiringHomomorphism_1290 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringHomomorphism.isRelHomomorphism
d_isRelHomomorphism_2042 ::
  T_IsSemiringHomomorphism_1282 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2042 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_'43''45'isMonoidHomomorphism_924
            (coe d_isNearSemiringHomomorphism_1290 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringHomomorphism.cong
d_cong_2044 ::
  T_IsSemiringHomomorphism_1282 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2044 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe
               d_'43''45'isMonoidHomomorphism_924
               (coe d_isNearSemiringHomomorphism_1290 (coe v0)))))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.*-homo
d_'42''45'homo_2048 ::
  T_IsSemiringIsomorphism_1364 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_2048 v0
  = coe
      d_'42''45'homo_926
      (coe
         d_isNearSemiringHomomorphism_1290
         (coe
            d_isSemiringHomomorphism_1324
            (coe d_isSemiringMonomorphism_1372 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_2050 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1364 -> T_IsMagmaHomomorphism_176
d_'42''45'isMagmaHomomorphism_2050 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_2050 v7
du_'42''45'isMagmaHomomorphism_2050 ::
  T_IsSemiringIsomorphism_1364 -> T_IsMagmaHomomorphism_176
du_'42''45'isMagmaHomomorphism_2050 v0
  = let v1 = d_isSemiringMonomorphism_1372 (coe v0) in
    coe
      (let v2 = d_isSemiringHomomorphism_1324 (coe v1) in
       coe
         (coe
            du_'42''45'isMagmaHomomorphism_940
            (coe d_isNearSemiringHomomorphism_1290 (coe v2))))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.*-isMagmaIsomorphism
d_'42''45'isMagmaIsomorphism_2052 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1364 -> T_IsMagmaIsomorphism_218
d_'42''45'isMagmaIsomorphism_2052 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaIsomorphism_2052 v7
du_'42''45'isMagmaIsomorphism_2052 ::
  T_IsSemiringIsomorphism_1364 -> T_IsMagmaIsomorphism_218
du_'42''45'isMagmaIsomorphism_2052 v0
  = coe
      du_'42''45'isMagmaIsomorphism_1036
      (coe du_isNearSemiringIsomorphism_1412 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.*-isMagmaMonomorphism
d_'42''45'isMagmaMonomorphism_2054 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1364 -> T_IsMagmaMonomorphism_194
d_'42''45'isMagmaMonomorphism_2054 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaMonomorphism_2054 v7
du_'42''45'isMagmaMonomorphism_2054 ::
  T_IsSemiringIsomorphism_1364 -> T_IsMagmaMonomorphism_194
du_'42''45'isMagmaMonomorphism_2054 v0
  = let v1 = d_isSemiringMonomorphism_1372 (coe v0) in
    coe
      (coe
         du_'42''45'isMagmaMonomorphism_982
         (coe du_isNearSemiringMonomorphism_1352 (coe v1)))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.*-isMonoidHomomorphism
d_'42''45'isMonoidHomomorphism_2056 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1364 -> T_IsMonoidHomomorphism_350
d_'42''45'isMonoidHomomorphism_2056 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidHomomorphism_2056 v7
du_'42''45'isMonoidHomomorphism_2056 ::
  T_IsSemiringIsomorphism_1364 -> T_IsMonoidHomomorphism_350
du_'42''45'isMonoidHomomorphism_2056 v0
  = let v1 = d_isSemiringMonomorphism_1372 (coe v0) in
    coe
      (coe
         du_'42''45'isMonoidHomomorphism_1312
         (coe d_isSemiringHomomorphism_1324 (coe v1)))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.*-isMonoidIsomorphism
d_'42''45'isMonoidIsomorphism_2058 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1364 -> T_IsMonoidIsomorphism_404
d_'42''45'isMonoidIsomorphism_2058 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'42''45'isMonoidIsomorphism_2058
du_'42''45'isMonoidIsomorphism_2058 ::
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1364 -> T_IsMonoidIsomorphism_404
du_'42''45'isMonoidIsomorphism_2058 v0 v1
  = coe du_'42''45'isMonoidIsomorphism_1420 v1
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.*-isMonoidMonomorphism
d_'42''45'isMonoidMonomorphism_2060 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1364 -> T_IsMonoidMonomorphism_372
d_'42''45'isMonoidMonomorphism_2060 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidMonomorphism_2060 v7
du_'42''45'isMonoidMonomorphism_2060 ::
  T_IsSemiringIsomorphism_1364 -> T_IsMonoidMonomorphism_372
du_'42''45'isMonoidMonomorphism_2060 v0
  = coe
      du_'42''45'isMonoidMonomorphism_1360
      (coe d_isSemiringMonomorphism_1372 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.homo
d_homo_2062 ::
  T_IsSemiringIsomorphism_1364 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2062 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_'43''45'isMonoidHomomorphism_924
            (coe
               d_isNearSemiringHomomorphism_1290
               (coe
                  d_isSemiringHomomorphism_1324
                  (coe d_isSemiringMonomorphism_1372 (coe v0))))))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_2064 ::
  T_IsSemiringIsomorphism_1364 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_2064 v0
  = coe
      d_isMagmaHomomorphism_358
      (coe
         d_'43''45'isMonoidHomomorphism_924
         (coe
            d_isNearSemiringHomomorphism_1290
            (coe
               d_isSemiringHomomorphism_1324
               (coe d_isSemiringMonomorphism_1372 (coe v0)))))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_2066 ::
  T_IsSemiringIsomorphism_1364 -> T_IsMonoidHomomorphism_350
d_'43''45'isMonoidHomomorphism_2066 v0
  = coe
      d_'43''45'isMonoidHomomorphism_924
      (coe
         d_isNearSemiringHomomorphism_1290
         (coe
            d_isSemiringHomomorphism_1324
            (coe d_isSemiringMonomorphism_1372 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.+-isMonoidIsomorphism
d_'43''45'isMonoidIsomorphism_2068 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1364 -> T_IsMonoidIsomorphism_404
d_'43''45'isMonoidIsomorphism_2068 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isMonoidIsomorphism_2068 v7
du_'43''45'isMonoidIsomorphism_2068 ::
  T_IsSemiringIsomorphism_1364 -> T_IsMonoidIsomorphism_404
du_'43''45'isMonoidIsomorphism_2068 v0
  = coe
      du_'43''45'isMonoidIsomorphism_1028
      (coe du_isNearSemiringIsomorphism_1412 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.+-isMonoidMonomorphism
d_'43''45'isMonoidMonomorphism_2070 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1364 -> T_IsMonoidMonomorphism_372
d_'43''45'isMonoidMonomorphism_2070 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isMonoidMonomorphism_2070 v7
du_'43''45'isMonoidMonomorphism_2070 ::
  T_IsSemiringIsomorphism_1364 -> T_IsMonoidMonomorphism_372
du_'43''45'isMonoidMonomorphism_2070 v0
  = let v1 = d_isSemiringMonomorphism_1372 (coe v0) in
    coe
      (coe
         du_'43''45'isMonoidMonomorphism_974
         (coe du_isNearSemiringMonomorphism_1352 (coe v1)))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.ε-homo
d_ε'45'homo_2072 :: T_IsSemiringIsomorphism_1364 -> AgdaAny
d_ε'45'homo_2072 v0
  = coe
      d_ε'45'homo_360
      (coe
         d_'43''45'isMonoidHomomorphism_924
         (coe
            d_isNearSemiringHomomorphism_1290
            (coe
               d_isSemiringHomomorphism_1324
               (coe d_isSemiringMonomorphism_1372 (coe v0)))))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.1#-homo
d_1'35''45'homo_2074 :: T_IsSemiringIsomorphism_1364 -> AgdaAny
d_1'35''45'homo_2074 v0
  = coe
      d_1'35''45'homo_1292
      (coe
         d_isSemiringHomomorphism_1324
         (coe d_isSemiringMonomorphism_1372 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.injective
d_injective_2076 ::
  T_IsSemiringIsomorphism_1364 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_2076 v0
  = coe d_injective_1326 (coe d_isSemiringMonomorphism_1372 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_2078 ::
  T_IsSemiringIsomorphism_1364 -> T_IsNearSemiringHomomorphism_916
d_isNearSemiringHomomorphism_2078 v0
  = coe
      d_isNearSemiringHomomorphism_1290
      (coe
         d_isSemiringHomomorphism_1324
         (coe d_isSemiringMonomorphism_1372 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.isNearSemiringIsomorphism
d_isNearSemiringIsomorphism_2080 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1364 -> T_IsNearSemiringIsomorphism_986
d_isNearSemiringIsomorphism_2080 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isNearSemiringIsomorphism_2080
du_isNearSemiringIsomorphism_2080 ::
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1364 -> T_IsNearSemiringIsomorphism_986
du_isNearSemiringIsomorphism_2080 v0 v1
  = coe du_isNearSemiringIsomorphism_1412 v1
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.isNearSemiringMonomorphism
d_isNearSemiringMonomorphism_2082 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1364 -> T_IsNearSemiringMonomorphism_944
d_isNearSemiringMonomorphism_2082 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isNearSemiringMonomorphism_2082 v7
du_isNearSemiringMonomorphism_2082 ::
  T_IsSemiringIsomorphism_1364 -> T_IsNearSemiringMonomorphism_944
du_isNearSemiringMonomorphism_2082 v0
  = coe
      du_isNearSemiringMonomorphism_1352
      (coe d_isSemiringMonomorphism_1372 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.isRelHomomorphism
d_isRelHomomorphism_2084 ::
  T_IsSemiringIsomorphism_1364 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2084 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_'43''45'isMonoidHomomorphism_924
            (coe
               d_isNearSemiringHomomorphism_1290
               (coe
                  d_isSemiringHomomorphism_1324
                  (coe d_isSemiringMonomorphism_1372 (coe v0))))))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.isSemiringHomomorphism
d_isSemiringHomomorphism_2086 ::
  T_IsSemiringIsomorphism_1364 -> T_IsSemiringHomomorphism_1282
d_isSemiringHomomorphism_2086 v0
  = coe
      d_isSemiringHomomorphism_1324
      (coe d_isSemiringMonomorphism_1372 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.isSemiringMonomorphism
d_isSemiringMonomorphism_2088 ::
  T_IsSemiringIsomorphism_1364 -> T_IsSemiringMonomorphism_1316
d_isSemiringMonomorphism_2088 v0
  = coe d_isSemiringMonomorphism_1372 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.surjective
d_surjective_2090 ::
  T_IsSemiringIsomorphism_1364 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_2090 v0 = coe d_surjective_1374 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.cong
d_cong_2092 ::
  T_IsSemiringIsomorphism_1364 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2092 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe
               d_'43''45'isMonoidHomomorphism_924
               (coe
                  d_isNearSemiringHomomorphism_1290
                  (coe
                     d_isSemiringHomomorphism_1324
                     (coe d_isSemiringMonomorphism_1372 (coe v0)))))))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringMonomorphism.*-homo
d_'42''45'homo_2096 ::
  T_IsSemiringMonomorphism_1316 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_2096 v0
  = coe
      d_'42''45'homo_926
      (coe
         d_isNearSemiringHomomorphism_1290
         (coe d_isSemiringHomomorphism_1324 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringMonomorphism.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_2098 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1316 -> T_IsMagmaHomomorphism_176
d_'42''45'isMagmaHomomorphism_2098 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_2098 v7
du_'42''45'isMagmaHomomorphism_2098 ::
  T_IsSemiringMonomorphism_1316 -> T_IsMagmaHomomorphism_176
du_'42''45'isMagmaHomomorphism_2098 v0
  = let v1 = d_isSemiringHomomorphism_1324 (coe v0) in
    coe
      (coe
         du_'42''45'isMagmaHomomorphism_940
         (coe d_isNearSemiringHomomorphism_1290 (coe v1)))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringMonomorphism.*-isMagmaMonomorphism
d_'42''45'isMagmaMonomorphism_2100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1316 -> T_IsMagmaMonomorphism_194
d_'42''45'isMagmaMonomorphism_2100 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaMonomorphism_2100 v7
du_'42''45'isMagmaMonomorphism_2100 ::
  T_IsSemiringMonomorphism_1316 -> T_IsMagmaMonomorphism_194
du_'42''45'isMagmaMonomorphism_2100 v0
  = coe
      du_'42''45'isMagmaMonomorphism_982
      (coe du_isNearSemiringMonomorphism_1352 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringMonomorphism.*-isMonoidHomomorphism
d_'42''45'isMonoidHomomorphism_2102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1316 -> T_IsMonoidHomomorphism_350
d_'42''45'isMonoidHomomorphism_2102 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidHomomorphism_2102 v7
du_'42''45'isMonoidHomomorphism_2102 ::
  T_IsSemiringMonomorphism_1316 -> T_IsMonoidHomomorphism_350
du_'42''45'isMonoidHomomorphism_2102 v0
  = coe
      du_'42''45'isMonoidHomomorphism_1312
      (coe d_isSemiringHomomorphism_1324 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringMonomorphism.*-isMonoidMonomorphism
d_'42''45'isMonoidMonomorphism_2104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1316 -> T_IsMonoidMonomorphism_372
d_'42''45'isMonoidMonomorphism_2104 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'42''45'isMonoidMonomorphism_2104
du_'42''45'isMonoidMonomorphism_2104 ::
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1316 -> T_IsMonoidMonomorphism_372
du_'42''45'isMonoidMonomorphism_2104 v0 v1
  = coe du_'42''45'isMonoidMonomorphism_1360 v1
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringMonomorphism.homo
d_homo_2106 ::
  T_IsSemiringMonomorphism_1316 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2106 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_'43''45'isMonoidHomomorphism_924
            (coe
               d_isNearSemiringHomomorphism_1290
               (coe d_isSemiringHomomorphism_1324 (coe v0)))))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_2108 ::
  T_IsSemiringMonomorphism_1316 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_2108 v0
  = coe
      d_isMagmaHomomorphism_358
      (coe
         d_'43''45'isMonoidHomomorphism_924
         (coe
            d_isNearSemiringHomomorphism_1290
            (coe d_isSemiringHomomorphism_1324 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringMonomorphism.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_2110 ::
  T_IsSemiringMonomorphism_1316 -> T_IsMonoidHomomorphism_350
d_'43''45'isMonoidHomomorphism_2110 v0
  = coe
      d_'43''45'isMonoidHomomorphism_924
      (coe
         d_isNearSemiringHomomorphism_1290
         (coe d_isSemiringHomomorphism_1324 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringMonomorphism.+-isMonoidMonomorphism
d_'43''45'isMonoidMonomorphism_2112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1316 -> T_IsMonoidMonomorphism_372
d_'43''45'isMonoidMonomorphism_2112 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isMonoidMonomorphism_2112 v7
du_'43''45'isMonoidMonomorphism_2112 ::
  T_IsSemiringMonomorphism_1316 -> T_IsMonoidMonomorphism_372
du_'43''45'isMonoidMonomorphism_2112 v0
  = coe
      du_'43''45'isMonoidMonomorphism_974
      (coe du_isNearSemiringMonomorphism_1352 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringMonomorphism.ε-homo
d_ε'45'homo_2114 :: T_IsSemiringMonomorphism_1316 -> AgdaAny
d_ε'45'homo_2114 v0
  = coe
      d_ε'45'homo_360
      (coe
         d_'43''45'isMonoidHomomorphism_924
         (coe
            d_isNearSemiringHomomorphism_1290
            (coe d_isSemiringHomomorphism_1324 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringMonomorphism.1#-homo
d_1'35''45'homo_2116 :: T_IsSemiringMonomorphism_1316 -> AgdaAny
d_1'35''45'homo_2116 v0
  = coe
      d_1'35''45'homo_1292 (coe d_isSemiringHomomorphism_1324 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringMonomorphism.injective
d_injective_2118 ::
  T_IsSemiringMonomorphism_1316 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_2118 v0 = coe d_injective_1326 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringMonomorphism.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_2120 ::
  T_IsSemiringMonomorphism_1316 -> T_IsNearSemiringHomomorphism_916
d_isNearSemiringHomomorphism_2120 v0
  = coe
      d_isNearSemiringHomomorphism_1290
      (coe d_isSemiringHomomorphism_1324 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringMonomorphism.isNearSemiringMonomorphism
d_isNearSemiringMonomorphism_2122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1316 -> T_IsNearSemiringMonomorphism_944
d_isNearSemiringMonomorphism_2122 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isNearSemiringMonomorphism_2122
du_isNearSemiringMonomorphism_2122 ::
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1316 -> T_IsNearSemiringMonomorphism_944
du_isNearSemiringMonomorphism_2122 v0 v1
  = coe du_isNearSemiringMonomorphism_1352 v1
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringMonomorphism.isRelHomomorphism
d_isRelHomomorphism_2124 ::
  T_IsSemiringMonomorphism_1316 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2124 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_'43''45'isMonoidHomomorphism_924
            (coe
               d_isNearSemiringHomomorphism_1290
               (coe d_isSemiringHomomorphism_1324 (coe v0)))))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringMonomorphism.isSemiringHomomorphism
d_isSemiringHomomorphism_2126 ::
  T_IsSemiringMonomorphism_1316 -> T_IsSemiringHomomorphism_1282
d_isSemiringHomomorphism_2126 v0
  = coe d_isSemiringHomomorphism_1324 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringMonomorphism.cong
d_cong_2128 ::
  T_IsSemiringMonomorphism_1316 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2128 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe
               d_'43''45'isMonoidHomomorphism_924
               (coe
                  d_isNearSemiringHomomorphism_1290
                  (coe d_isSemiringHomomorphism_1324 (coe v0))))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingHomomorphism
d_IsRingHomomorphism_2132 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsRingHomomorphism_2132
  = C_IsRingHomomorphism'46'constructor_41447 T_IsSemiringHomomorphism_1282
                                              (AgdaAny -> AgdaAny)
-- Algebra.Morphism.Structures.RingMorphisms.IsRingHomomorphism.isSemiringHomomorphism
d_isSemiringHomomorphism_2140 ::
  T_IsRingHomomorphism_2132 -> T_IsSemiringHomomorphism_1282
d_isSemiringHomomorphism_2140 v0
  = case coe v0 of
      C_IsRingHomomorphism'46'constructor_41447 v1 v2 -> coe v1
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.RingMorphisms.IsRingHomomorphism.-‿homo
d_'45''8255'homo_2142 ::
  T_IsRingHomomorphism_2132 -> AgdaAny -> AgdaAny
d_'45''8255'homo_2142 v0
  = case coe v0 of
      C_IsRingHomomorphism'46'constructor_41447 v1 v2 -> coe v2
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.RingMorphisms.IsRingHomomorphism._.*-homo
d_'42''45'homo_2146 ::
  T_IsRingHomomorphism_2132 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_2146 v0
  = coe
      d_'42''45'homo_926
      (coe
         d_isNearSemiringHomomorphism_1290
         (coe d_isSemiringHomomorphism_2140 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingHomomorphism._.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_2148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingHomomorphism_2132 -> T_IsMagmaHomomorphism_176
d_'42''45'isMagmaHomomorphism_2148 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_2148 v7
du_'42''45'isMagmaHomomorphism_2148 ::
  T_IsRingHomomorphism_2132 -> T_IsMagmaHomomorphism_176
du_'42''45'isMagmaHomomorphism_2148 v0
  = let v1 = d_isSemiringHomomorphism_2140 (coe v0) in
    coe
      (coe
         du_'42''45'isMagmaHomomorphism_940
         (coe d_isNearSemiringHomomorphism_1290 (coe v1)))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingHomomorphism._.*-isMonoidHomomorphism
d_'42''45'isMonoidHomomorphism_2150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingHomomorphism_2132 -> T_IsMonoidHomomorphism_350
d_'42''45'isMonoidHomomorphism_2150 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidHomomorphism_2150 v7
du_'42''45'isMonoidHomomorphism_2150 ::
  T_IsRingHomomorphism_2132 -> T_IsMonoidHomomorphism_350
du_'42''45'isMonoidHomomorphism_2150 v0
  = coe
      du_'42''45'isMonoidHomomorphism_1312
      (coe d_isSemiringHomomorphism_2140 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingHomomorphism._.homo
d_homo_2152 ::
  T_IsRingHomomorphism_2132 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2152 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_'43''45'isMonoidHomomorphism_924
            (coe
               d_isNearSemiringHomomorphism_1290
               (coe d_isSemiringHomomorphism_2140 (coe v0)))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingHomomorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_2154 ::
  T_IsRingHomomorphism_2132 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_2154 v0
  = coe
      d_isMagmaHomomorphism_358
      (coe
         d_'43''45'isMonoidHomomorphism_924
         (coe
            d_isNearSemiringHomomorphism_1290
            (coe d_isSemiringHomomorphism_2140 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingHomomorphism._.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_2156 ::
  T_IsRingHomomorphism_2132 -> T_IsMonoidHomomorphism_350
d_'43''45'isMonoidHomomorphism_2156 v0
  = coe
      d_'43''45'isMonoidHomomorphism_924
      (coe
         d_isNearSemiringHomomorphism_1290
         (coe d_isSemiringHomomorphism_2140 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingHomomorphism._.ε-homo
d_ε'45'homo_2158 :: T_IsRingHomomorphism_2132 -> AgdaAny
d_ε'45'homo_2158 v0
  = coe
      d_ε'45'homo_360
      (coe
         d_'43''45'isMonoidHomomorphism_924
         (coe
            d_isNearSemiringHomomorphism_1290
            (coe d_isSemiringHomomorphism_2140 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingHomomorphism._.1#-homo
d_1'35''45'homo_2160 :: T_IsRingHomomorphism_2132 -> AgdaAny
d_1'35''45'homo_2160 v0
  = coe
      d_1'35''45'homo_1292 (coe d_isSemiringHomomorphism_2140 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingHomomorphism._.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_2162 ::
  T_IsRingHomomorphism_2132 -> T_IsNearSemiringHomomorphism_916
d_isNearSemiringHomomorphism_2162 v0
  = coe
      d_isNearSemiringHomomorphism_1290
      (coe d_isSemiringHomomorphism_2140 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingHomomorphism._.isRelHomomorphism
d_isRelHomomorphism_2164 ::
  T_IsRingHomomorphism_2132 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2164 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_'43''45'isMonoidHomomorphism_924
            (coe
               d_isNearSemiringHomomorphism_1290
               (coe d_isSemiringHomomorphism_2140 (coe v0)))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingHomomorphism._.cong
d_cong_2166 ::
  T_IsRingHomomorphism_2132 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2166 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe
               d_'43''45'isMonoidHomomorphism_924
               (coe
                  d_isNearSemiringHomomorphism_1290
                  (coe d_isSemiringHomomorphism_2140 (coe v0))))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingHomomorphism.+-isGroupHomomorphism
d_'43''45'isGroupHomomorphism_2168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingHomomorphism_2132 -> T_IsGroupHomomorphism_622
d_'43''45'isGroupHomomorphism_2168 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isGroupHomomorphism_2168 v7
du_'43''45'isGroupHomomorphism_2168 ::
  T_IsRingHomomorphism_2132 -> T_IsGroupHomomorphism_622
du_'43''45'isGroupHomomorphism_2168 v0
  = coe
      C_IsGroupHomomorphism'46'constructor_14585
      (coe
         d_'43''45'isMonoidHomomorphism_924
         (coe
            d_isNearSemiringHomomorphism_1290
            (coe d_isSemiringHomomorphism_2140 (coe v0))))
      (coe d_'45''8255'homo_2142 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism
d_IsRingMonomorphism_2172 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsRingMonomorphism_2172
  = C_IsRingMonomorphism'46'constructor_42933 T_IsRingHomomorphism_2132
                                              (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism.isRingHomomorphism
d_isRingHomomorphism_2180 ::
  T_IsRingMonomorphism_2172 -> T_IsRingHomomorphism_2132
d_isRingHomomorphism_2180 v0
  = case coe v0 of
      C_IsRingMonomorphism'46'constructor_42933 v1 v2 -> coe v1
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism.injective
d_injective_2182 ::
  T_IsRingMonomorphism_2172 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_2182 v0
  = case coe v0 of
      C_IsRingMonomorphism'46'constructor_42933 v1 v2 -> coe v2
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism._.*-homo
d_'42''45'homo_2186 ::
  T_IsRingMonomorphism_2172 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_2186 v0
  = coe
      d_'42''45'homo_926
      (coe
         d_isNearSemiringHomomorphism_1290
         (coe
            d_isSemiringHomomorphism_2140
            (coe d_isRingHomomorphism_2180 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism._.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_2188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingMonomorphism_2172 -> T_IsMagmaHomomorphism_176
d_'42''45'isMagmaHomomorphism_2188 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_2188 v7
du_'42''45'isMagmaHomomorphism_2188 ::
  T_IsRingMonomorphism_2172 -> T_IsMagmaHomomorphism_176
du_'42''45'isMagmaHomomorphism_2188 v0
  = let v1 = d_isRingHomomorphism_2180 (coe v0) in
    coe
      (let v2 = d_isSemiringHomomorphism_2140 (coe v1) in
       coe
         (coe
            du_'42''45'isMagmaHomomorphism_940
            (coe d_isNearSemiringHomomorphism_1290 (coe v2))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism._.*-isMonoidHomomorphism
d_'42''45'isMonoidHomomorphism_2190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingMonomorphism_2172 -> T_IsMonoidHomomorphism_350
d_'42''45'isMonoidHomomorphism_2190 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidHomomorphism_2190 v7
du_'42''45'isMonoidHomomorphism_2190 ::
  T_IsRingMonomorphism_2172 -> T_IsMonoidHomomorphism_350
du_'42''45'isMonoidHomomorphism_2190 v0
  = let v1 = d_isRingHomomorphism_2180 (coe v0) in
    coe
      (coe
         du_'42''45'isMonoidHomomorphism_1312
         (coe d_isSemiringHomomorphism_2140 (coe v1)))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism._.homo
d_homo_2192 ::
  T_IsRingMonomorphism_2172 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2192 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_'43''45'isMonoidHomomorphism_924
            (coe
               d_isNearSemiringHomomorphism_1290
               (coe
                  d_isSemiringHomomorphism_2140
                  (coe d_isRingHomomorphism_2180 (coe v0))))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism._.+-isGroupHomomorphism
d_'43''45'isGroupHomomorphism_2194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingMonomorphism_2172 -> T_IsGroupHomomorphism_622
d_'43''45'isGroupHomomorphism_2194 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isGroupHomomorphism_2194 v7
du_'43''45'isGroupHomomorphism_2194 ::
  T_IsRingMonomorphism_2172 -> T_IsGroupHomomorphism_622
du_'43''45'isGroupHomomorphism_2194 v0
  = coe
      du_'43''45'isGroupHomomorphism_2168
      (coe d_isRingHomomorphism_2180 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_2196 ::
  T_IsRingMonomorphism_2172 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_2196 v0
  = coe
      d_isMagmaHomomorphism_358
      (coe
         d_'43''45'isMonoidHomomorphism_924
         (coe
            d_isNearSemiringHomomorphism_1290
            (coe
               d_isSemiringHomomorphism_2140
               (coe d_isRingHomomorphism_2180 (coe v0)))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism._.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_2198 ::
  T_IsRingMonomorphism_2172 -> T_IsMonoidHomomorphism_350
d_'43''45'isMonoidHomomorphism_2198 v0
  = coe
      d_'43''45'isMonoidHomomorphism_924
      (coe
         d_isNearSemiringHomomorphism_1290
         (coe
            d_isSemiringHomomorphism_2140
            (coe d_isRingHomomorphism_2180 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism._.-‿homo
d_'45''8255'homo_2200 ::
  T_IsRingMonomorphism_2172 -> AgdaAny -> AgdaAny
d_'45''8255'homo_2200 v0
  = coe
      d_'45''8255'homo_2142 (coe d_isRingHomomorphism_2180 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism._.ε-homo
d_ε'45'homo_2202 :: T_IsRingMonomorphism_2172 -> AgdaAny
d_ε'45'homo_2202 v0
  = coe
      d_ε'45'homo_360
      (coe
         d_'43''45'isMonoidHomomorphism_924
         (coe
            d_isNearSemiringHomomorphism_1290
            (coe
               d_isSemiringHomomorphism_2140
               (coe d_isRingHomomorphism_2180 (coe v0)))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism._.1#-homo
d_1'35''45'homo_2204 :: T_IsRingMonomorphism_2172 -> AgdaAny
d_1'35''45'homo_2204 v0
  = coe
      d_1'35''45'homo_1292
      (coe
         d_isSemiringHomomorphism_2140
         (coe d_isRingHomomorphism_2180 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism._.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_2206 ::
  T_IsRingMonomorphism_2172 -> T_IsNearSemiringHomomorphism_916
d_isNearSemiringHomomorphism_2206 v0
  = coe
      d_isNearSemiringHomomorphism_1290
      (coe
         d_isSemiringHomomorphism_2140
         (coe d_isRingHomomorphism_2180 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism._.isRelHomomorphism
d_isRelHomomorphism_2208 ::
  T_IsRingMonomorphism_2172 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2208 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_'43''45'isMonoidHomomorphism_924
            (coe
               d_isNearSemiringHomomorphism_1290
               (coe
                  d_isSemiringHomomorphism_2140
                  (coe d_isRingHomomorphism_2180 (coe v0))))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism._.isSemiringHomomorphism
d_isSemiringHomomorphism_2210 ::
  T_IsRingMonomorphism_2172 -> T_IsSemiringHomomorphism_1282
d_isSemiringHomomorphism_2210 v0
  = coe
      d_isSemiringHomomorphism_2140
      (coe d_isRingHomomorphism_2180 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism._.cong
d_cong_2212 ::
  T_IsRingMonomorphism_2172 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2212 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe
               d_'43''45'isMonoidHomomorphism_924
               (coe
                  d_isNearSemiringHomomorphism_1290
                  (coe
                     d_isSemiringHomomorphism_2140
                     (coe d_isRingHomomorphism_2180 (coe v0)))))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism.isSemiringMonomorphism
d_isSemiringMonomorphism_2214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingMonomorphism_2172 -> T_IsSemiringMonomorphism_1316
d_isSemiringMonomorphism_2214 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isSemiringMonomorphism_2214 v7
du_isSemiringMonomorphism_2214 ::
  T_IsRingMonomorphism_2172 -> T_IsSemiringMonomorphism_1316
du_isSemiringMonomorphism_2214 v0
  = coe
      C_IsSemiringMonomorphism'46'constructor_27871
      (coe
         d_isSemiringHomomorphism_2140
         (coe d_isRingHomomorphism_2180 (coe v0)))
      (coe d_injective_2182 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism.+-isGroupMonomorphism
d_'43''45'isGroupMonomorphism_2216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingMonomorphism_2172 -> T_IsGroupMonomorphism_648
d_'43''45'isGroupMonomorphism_2216 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isGroupMonomorphism_2216 v7
du_'43''45'isGroupMonomorphism_2216 ::
  T_IsRingMonomorphism_2172 -> T_IsGroupMonomorphism_648
du_'43''45'isGroupMonomorphism_2216 v0
  = coe
      C_IsGroupMonomorphism'46'constructor_15537
      (coe
         du_'43''45'isGroupHomomorphism_2168
         (coe d_isRingHomomorphism_2180 (coe v0)))
      (coe d_injective_2182 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism._.isMagmaMonomorphism
d_isMagmaMonomorphism_2220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingMonomorphism_2172 -> T_IsMagmaMonomorphism_194
d_isMagmaMonomorphism_2220 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_2220 v7
du_isMagmaMonomorphism_2220 ::
  T_IsRingMonomorphism_2172 -> T_IsMagmaMonomorphism_194
du_isMagmaMonomorphism_2220 v0
  = let v1 = coe du_'43''45'isGroupMonomorphism_2216 (coe v0) in
    coe
      (coe
         du_isMagmaMonomorphism_396
         (coe du_isMonoidMonomorphism_676 (coe v1)))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism._.isMonoidMonomorphism
d_isMonoidMonomorphism_2222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingMonomorphism_2172 -> T_IsMonoidMonomorphism_372
d_isMonoidMonomorphism_2222 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMonoidMonomorphism_2222 v7
du_isMonoidMonomorphism_2222 ::
  T_IsRingMonomorphism_2172 -> T_IsMonoidMonomorphism_372
du_isMonoidMonomorphism_2222 v0
  = coe
      du_isMonoidMonomorphism_676
      (coe du_'43''45'isGroupMonomorphism_2216 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism._.isRelMonomorphism
d_isRelMonomorphism_2224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingMonomorphism_2172 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_2224 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_2224 v7
du_isRelMonomorphism_2224 ::
  T_IsRingMonomorphism_2172 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_2224 v0
  = let v1 = coe du_'43''45'isGroupMonomorphism_2216 (coe v0) in
    coe
      (let v2 = coe du_isMonoidMonomorphism_676 (coe v1) in
       coe
         (coe
            du_isRelMonomorphism_214
            (coe du_isMagmaMonomorphism_396 (coe v2))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism.*-isMonoidMonomorphism
d_'42''45'isMonoidMonomorphism_2226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingMonomorphism_2172 -> T_IsMonoidMonomorphism_372
d_'42''45'isMonoidMonomorphism_2226 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidMonomorphism_2226 v7
du_'42''45'isMonoidMonomorphism_2226 ::
  T_IsRingMonomorphism_2172 -> T_IsMonoidMonomorphism_372
du_'42''45'isMonoidMonomorphism_2226 v0
  = coe
      C_IsMonoidMonomorphism'46'constructor_10237
      (coe
         du_'42''45'isMonoidHomomorphism_1312
         (coe
            d_isSemiringHomomorphism_2140
            (coe d_isRingHomomorphism_2180 (coe v0))))
      (coe d_injective_2182 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism._.isMagmaMonomorphism
d_isMagmaMonomorphism_2230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingMonomorphism_2172 -> T_IsMagmaMonomorphism_194
d_isMagmaMonomorphism_2230 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_2230 v7
du_isMagmaMonomorphism_2230 ::
  T_IsRingMonomorphism_2172 -> T_IsMagmaMonomorphism_194
du_isMagmaMonomorphism_2230 v0
  = coe
      du_isMagmaMonomorphism_396
      (coe du_'42''45'isMonoidMonomorphism_2226 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism
d_IsRingIsomorphism_2234 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsRingIsomorphism_2234
  = C_IsRingIsomorphism'46'constructor_45617 T_IsRingMonomorphism_2172
                                             (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism.isRingMonomorphism
d_isRingMonomorphism_2242 ::
  T_IsRingIsomorphism_2234 -> T_IsRingMonomorphism_2172
d_isRingMonomorphism_2242 v0
  = case coe v0 of
      C_IsRingIsomorphism'46'constructor_45617 v1 v2 -> coe v1
      _                                              -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism.surjective
d_surjective_2244 ::
  T_IsRingIsomorphism_2234 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_2244 v0
  = case coe v0 of
      C_IsRingIsomorphism'46'constructor_45617 v1 v2 -> coe v2
      _                                              -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.*-homo
d_'42''45'homo_2248 ::
  T_IsRingIsomorphism_2234 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_2248 v0
  = coe
      d_'42''45'homo_926
      (coe
         d_isNearSemiringHomomorphism_1290
         (coe
            d_isSemiringHomomorphism_2140
            (coe
               d_isRingHomomorphism_2180
               (coe d_isRingMonomorphism_2242 (coe v0)))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_2250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingIsomorphism_2234 -> T_IsMagmaHomomorphism_176
d_'42''45'isMagmaHomomorphism_2250 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_2250 v7
du_'42''45'isMagmaHomomorphism_2250 ::
  T_IsRingIsomorphism_2234 -> T_IsMagmaHomomorphism_176
du_'42''45'isMagmaHomomorphism_2250 v0
  = let v1 = d_isRingMonomorphism_2242 (coe v0) in
    coe
      (let v2 = d_isRingHomomorphism_2180 (coe v1) in
       coe
         (let v3 = d_isSemiringHomomorphism_2140 (coe v2) in
          coe
            (coe
               du_'42''45'isMagmaHomomorphism_940
               (coe d_isNearSemiringHomomorphism_1290 (coe v3)))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.isMagmaMonomorphism
d_isMagmaMonomorphism_2252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingIsomorphism_2234 -> T_IsMagmaMonomorphism_194
d_isMagmaMonomorphism_2252 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_2252 v7
du_isMagmaMonomorphism_2252 ::
  T_IsRingIsomorphism_2234 -> T_IsMagmaMonomorphism_194
du_isMagmaMonomorphism_2252 v0
  = let v1 = d_isRingMonomorphism_2242 (coe v0) in
    coe
      (coe
         du_isMagmaMonomorphism_396
         (coe du_'42''45'isMonoidMonomorphism_2226 (coe v1)))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.*-isMonoidHomomorphism
d_'42''45'isMonoidHomomorphism_2254 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingIsomorphism_2234 -> T_IsMonoidHomomorphism_350
d_'42''45'isMonoidHomomorphism_2254 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidHomomorphism_2254 v7
du_'42''45'isMonoidHomomorphism_2254 ::
  T_IsRingIsomorphism_2234 -> T_IsMonoidHomomorphism_350
du_'42''45'isMonoidHomomorphism_2254 v0
  = let v1 = d_isRingMonomorphism_2242 (coe v0) in
    coe
      (let v2 = d_isRingHomomorphism_2180 (coe v1) in
       coe
         (coe
            du_'42''45'isMonoidHomomorphism_1312
            (coe d_isSemiringHomomorphism_2140 (coe v2))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.*-isMonoidMonomorphism
d_'42''45'isMonoidMonomorphism_2256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingIsomorphism_2234 -> T_IsMonoidMonomorphism_372
d_'42''45'isMonoidMonomorphism_2256 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidMonomorphism_2256 v7
du_'42''45'isMonoidMonomorphism_2256 ::
  T_IsRingIsomorphism_2234 -> T_IsMonoidMonomorphism_372
du_'42''45'isMonoidMonomorphism_2256 v0
  = coe
      du_'42''45'isMonoidMonomorphism_2226
      (coe d_isRingMonomorphism_2242 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.homo
d_homo_2258 ::
  T_IsRingIsomorphism_2234 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2258 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_'43''45'isMonoidHomomorphism_924
            (coe
               d_isNearSemiringHomomorphism_1290
               (coe
                  d_isSemiringHomomorphism_2140
                  (coe
                     d_isRingHomomorphism_2180
                     (coe d_isRingMonomorphism_2242 (coe v0)))))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.+-isGroupHomomorphism
d_'43''45'isGroupHomomorphism_2260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingIsomorphism_2234 -> T_IsGroupHomomorphism_622
d_'43''45'isGroupHomomorphism_2260 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isGroupHomomorphism_2260 v7
du_'43''45'isGroupHomomorphism_2260 ::
  T_IsRingIsomorphism_2234 -> T_IsGroupHomomorphism_622
du_'43''45'isGroupHomomorphism_2260 v0
  = let v1 = d_isRingMonomorphism_2242 (coe v0) in
    coe
      (coe
         du_'43''45'isGroupHomomorphism_2168
         (coe d_isRingHomomorphism_2180 (coe v1)))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.+-isGroupMonomorphism
d_'43''45'isGroupMonomorphism_2262 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingIsomorphism_2234 -> T_IsGroupMonomorphism_648
d_'43''45'isGroupMonomorphism_2262 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isGroupMonomorphism_2262 v7
du_'43''45'isGroupMonomorphism_2262 ::
  T_IsRingIsomorphism_2234 -> T_IsGroupMonomorphism_648
du_'43''45'isGroupMonomorphism_2262 v0
  = coe
      du_'43''45'isGroupMonomorphism_2216
      (coe d_isRingMonomorphism_2242 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_2264 ::
  T_IsRingIsomorphism_2234 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_2264 v0
  = coe
      d_isMagmaHomomorphism_358
      (coe
         d_'43''45'isMonoidHomomorphism_924
         (coe
            d_isNearSemiringHomomorphism_1290
            (coe
               d_isSemiringHomomorphism_2140
               (coe
                  d_isRingHomomorphism_2180
                  (coe d_isRingMonomorphism_2242 (coe v0))))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_2266 ::
  T_IsRingIsomorphism_2234 -> T_IsMonoidHomomorphism_350
d_'43''45'isMonoidHomomorphism_2266 v0
  = coe
      d_'43''45'isMonoidHomomorphism_924
      (coe
         d_isNearSemiringHomomorphism_1290
         (coe
            d_isSemiringHomomorphism_2140
            (coe
               d_isRingHomomorphism_2180
               (coe d_isRingMonomorphism_2242 (coe v0)))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.-‿homo
d_'45''8255'homo_2268 ::
  T_IsRingIsomorphism_2234 -> AgdaAny -> AgdaAny
d_'45''8255'homo_2268 v0
  = coe
      d_'45''8255'homo_2142
      (coe
         d_isRingHomomorphism_2180 (coe d_isRingMonomorphism_2242 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.ε-homo
d_ε'45'homo_2270 :: T_IsRingIsomorphism_2234 -> AgdaAny
d_ε'45'homo_2270 v0
  = coe
      d_ε'45'homo_360
      (coe
         d_'43''45'isMonoidHomomorphism_924
         (coe
            d_isNearSemiringHomomorphism_1290
            (coe
               d_isSemiringHomomorphism_2140
               (coe
                  d_isRingHomomorphism_2180
                  (coe d_isRingMonomorphism_2242 (coe v0))))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.1#-homo
d_1'35''45'homo_2272 :: T_IsRingIsomorphism_2234 -> AgdaAny
d_1'35''45'homo_2272 v0
  = coe
      d_1'35''45'homo_1292
      (coe
         d_isSemiringHomomorphism_2140
         (coe
            d_isRingHomomorphism_2180
            (coe d_isRingMonomorphism_2242 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.injective
d_injective_2274 ::
  T_IsRingIsomorphism_2234 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_2274 v0
  = coe d_injective_2182 (coe d_isRingMonomorphism_2242 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_2276 ::
  T_IsRingIsomorphism_2234 -> T_IsNearSemiringHomomorphism_916
d_isNearSemiringHomomorphism_2276 v0
  = coe
      d_isNearSemiringHomomorphism_1290
      (coe
         d_isSemiringHomomorphism_2140
         (coe
            d_isRingHomomorphism_2180
            (coe d_isRingMonomorphism_2242 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.isRelHomomorphism
d_isRelHomomorphism_2278 ::
  T_IsRingIsomorphism_2234 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2278 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_'43''45'isMonoidHomomorphism_924
            (coe
               d_isNearSemiringHomomorphism_1290
               (coe
                  d_isSemiringHomomorphism_2140
                  (coe
                     d_isRingHomomorphism_2180
                     (coe d_isRingMonomorphism_2242 (coe v0)))))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.isRingHomomorphism
d_isRingHomomorphism_2280 ::
  T_IsRingIsomorphism_2234 -> T_IsRingHomomorphism_2132
d_isRingHomomorphism_2280 v0
  = coe
      d_isRingHomomorphism_2180 (coe d_isRingMonomorphism_2242 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.isSemiringHomomorphism
d_isSemiringHomomorphism_2282 ::
  T_IsRingIsomorphism_2234 -> T_IsSemiringHomomorphism_1282
d_isSemiringHomomorphism_2282 v0
  = coe
      d_isSemiringHomomorphism_2140
      (coe
         d_isRingHomomorphism_2180 (coe d_isRingMonomorphism_2242 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.isSemiringMonomorphism
d_isSemiringMonomorphism_2284 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingIsomorphism_2234 -> T_IsSemiringMonomorphism_1316
d_isSemiringMonomorphism_2284 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isSemiringMonomorphism_2284 v7
du_isSemiringMonomorphism_2284 ::
  T_IsRingIsomorphism_2234 -> T_IsSemiringMonomorphism_1316
du_isSemiringMonomorphism_2284 v0
  = coe
      du_isSemiringMonomorphism_2214
      (coe d_isRingMonomorphism_2242 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.cong
d_cong_2286 ::
  T_IsRingIsomorphism_2234 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2286 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe
               d_'43''45'isMonoidHomomorphism_924
               (coe
                  d_isNearSemiringHomomorphism_1290
                  (coe
                     d_isSemiringHomomorphism_2140
                     (coe
                        d_isRingHomomorphism_2180
                        (coe d_isRingMonomorphism_2242 (coe v0))))))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism.isSemiringIsomorphism
d_isSemiringIsomorphism_2288 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingIsomorphism_2234 -> T_IsSemiringIsomorphism_1364
d_isSemiringIsomorphism_2288 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isSemiringIsomorphism_2288 v7
du_isSemiringIsomorphism_2288 ::
  T_IsRingIsomorphism_2234 -> T_IsSemiringIsomorphism_1364
du_isSemiringIsomorphism_2288 v0
  = coe
      C_IsSemiringIsomorphism'46'constructor_29931
      (coe
         du_isSemiringMonomorphism_2214
         (coe d_isRingMonomorphism_2242 (coe v0)))
      (coe d_surjective_2244 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism.+-isGroupIsomorphism
d_'43''45'isGroupIsomorphism_2290 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingIsomorphism_2234 -> T_IsGroupIsomorphism_686
d_'43''45'isGroupIsomorphism_2290 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isGroupIsomorphism_2290 v7
du_'43''45'isGroupIsomorphism_2290 ::
  T_IsRingIsomorphism_2234 -> T_IsGroupIsomorphism_686
du_'43''45'isGroupIsomorphism_2290 v0
  = coe
      C_IsGroupIsomorphism'46'constructor_17073
      (coe
         du_'43''45'isGroupMonomorphism_2216
         (coe d_isRingMonomorphism_2242 (coe v0)))
      (coe d_surjective_2244 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.isMagmaIsomorphism
d_isMagmaIsomorphism_2294 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingIsomorphism_2234 -> T_IsMagmaIsomorphism_218
d_isMagmaIsomorphism_2294 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaIsomorphism_2294 v7
du_isMagmaIsomorphism_2294 ::
  T_IsRingIsomorphism_2234 -> T_IsMagmaIsomorphism_218
du_isMagmaIsomorphism_2294 v0
  = let v1 = coe du_'43''45'isGroupIsomorphism_2290 (coe v0) in
    coe
      (coe
         du_isMagmaIsomorphism_436
         (coe du_isMonoidIsomorphism_724 (coe v1)))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.isMonoidIsomorphism
d_isMonoidIsomorphism_2296 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingIsomorphism_2234 -> T_IsMonoidIsomorphism_404
d_isMonoidIsomorphism_2296 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMonoidIsomorphism_2296 v7
du_isMonoidIsomorphism_2296 ::
  T_IsRingIsomorphism_2234 -> T_IsMonoidIsomorphism_404
du_isMonoidIsomorphism_2296 v0
  = coe
      du_isMonoidIsomorphism_724
      (coe du_'43''45'isGroupIsomorphism_2290 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.isRelIsomorphism
d_isRelIsomorphism_2298 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingIsomorphism_2234 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
d_isRelIsomorphism_2298 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelIsomorphism_2298 v7
du_isRelIsomorphism_2298 ::
  T_IsRingIsomorphism_2234 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
du_isRelIsomorphism_2298 v0
  = let v1 = coe du_'43''45'isGroupIsomorphism_2290 (coe v0) in
    coe
      (let v2 = coe du_isMonoidIsomorphism_724 (coe v1) in
       coe
         (coe
            du_isRelIsomorphism_244 (coe du_isMagmaIsomorphism_436 (coe v2))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism.*-isMonoidIsomorphism
d_'42''45'isMonoidIsomorphism_2300 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingIsomorphism_2234 -> T_IsMonoidIsomorphism_404
d_'42''45'isMonoidIsomorphism_2300 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidIsomorphism_2300 v7
du_'42''45'isMonoidIsomorphism_2300 ::
  T_IsRingIsomorphism_2234 -> T_IsMonoidIsomorphism_404
du_'42''45'isMonoidIsomorphism_2300 v0
  = coe
      C_IsMonoidIsomorphism'46'constructor_11597
      (coe
         du_'42''45'isMonoidMonomorphism_2226
         (coe d_isRingMonomorphism_2242 (coe v0)))
      (coe d_surjective_2244 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.isMagmaIsomorphism
d_isMagmaIsomorphism_2304 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_268 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingIsomorphism_2234 -> T_IsMagmaIsomorphism_218
d_isMagmaIsomorphism_2304 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaIsomorphism_2304 v7
du_isMagmaIsomorphism_2304 ::
  T_IsRingIsomorphism_2234 -> T_IsMagmaIsomorphism_218
du_isMagmaIsomorphism_2304 v0
  = coe
      du_isMagmaIsomorphism_436
      (coe du_'42''45'isMonoidIsomorphism_2300 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms._._//_
d__'47''47'__2322 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'47''47'__2322 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du__'47''47'__2322 v4
du__'47''47'__2322 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'47''47'__2322 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d__'47''47'__350 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms._._\\_
d__'92''92'__2324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'92''92'__2324 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du__'92''92'__2324 v4
du__'92''92'__2324 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'92''92'__2324 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d__'92''92'__348 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms._._∙_
d__'8729'__2326 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'8729'__2326 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du__'8729'__2326 v4
du__'8729'__2326 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'8729'__2326 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__346 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms._._≈_
d__'8776'__2328 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__2328 = erased
-- Algebra.Morphism.Structures.QuasigroupMorphisms._.Carrier
d_Carrier_2334 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 -> ()
d_Carrier_2334 = erased
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaHomomorphism
d_IsMagmaHomomorphism_2362 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaIsomorphism
d_IsMagmaIsomorphism_2364 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaMonomorphism
d_IsMagmaMonomorphism_2366 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaHomomorphism.homo
d_homo_2370 ::
  T_IsMagmaHomomorphism_176 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2370 v0 = coe d_homo_186 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaHomomorphism.isRelHomomorphism
d_isRelHomomorphism_2372 ::
  T_IsMagmaHomomorphism_176 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2372 v0 = coe d_isRelHomomorphism_184 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaHomomorphism.cong
d_cong_2374 ::
  T_IsMagmaHomomorphism_176 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2374 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe d_isRelHomomorphism_184 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaIsomorphism.homo
d_homo_2378 ::
  T_IsMagmaIsomorphism_218 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2378 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_202 (coe d_isMagmaMonomorphism_226 (coe v0)))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaIsomorphism.injective
d_injective_2380 ::
  T_IsMagmaIsomorphism_218 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_2380 v0
  = coe d_injective_204 (coe d_isMagmaMonomorphism_226 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaIsomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_2382 ::
  T_IsMagmaIsomorphism_218 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_2382 v0
  = coe
      d_isMagmaHomomorphism_202 (coe d_isMagmaMonomorphism_226 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaIsomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_2384 ::
  T_IsMagmaIsomorphism_218 -> T_IsMagmaMonomorphism_194
d_isMagmaMonomorphism_2384 v0
  = coe d_isMagmaMonomorphism_226 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaIsomorphism.isRelHomomorphism
d_isRelHomomorphism_2386 ::
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2386 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_202 (coe d_isMagmaMonomorphism_226 (coe v0)))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaIsomorphism.isRelIsomorphism
d_isRelIsomorphism_2388 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
d_isRelIsomorphism_2388 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isRelIsomorphism_2388
du_isRelIsomorphism_2388 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
du_isRelIsomorphism_2388 v0 v1 = coe du_isRelIsomorphism_244 v1
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaIsomorphism.isRelMonomorphism
d_isRelMonomorphism_2390 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_2390 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_2390 v7
du_isRelMonomorphism_2390 ::
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_2390 v0
  = coe
      du_isRelMonomorphism_214 (coe d_isMagmaMonomorphism_226 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaIsomorphism.surjective
d_surjective_2392 ::
  T_IsMagmaIsomorphism_218 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_2392 v0 = coe d_surjective_228 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaIsomorphism.cong
d_cong_2394 ::
  T_IsMagmaIsomorphism_218 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2394 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_202
            (coe d_isMagmaMonomorphism_226 (coe v0))))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaMonomorphism.homo
d_homo_2398 ::
  T_IsMagmaMonomorphism_194 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2398 v0
  = coe d_homo_186 (coe d_isMagmaHomomorphism_202 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaMonomorphism.injective
d_injective_2400 ::
  T_IsMagmaMonomorphism_194 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_2400 v0 = coe d_injective_204 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_2402 ::
  T_IsMagmaMonomorphism_194 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_2402 v0
  = coe d_isMagmaHomomorphism_202 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaMonomorphism.isRelHomomorphism
d_isRelHomomorphism_2404 ::
  T_IsMagmaMonomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2404 v0
  = coe
      d_isRelHomomorphism_184 (coe d_isMagmaHomomorphism_202 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaMonomorphism.isRelMonomorphism
d_isRelMonomorphism_2406 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_2406 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isRelMonomorphism_2406
du_isRelMonomorphism_2406 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_2406 v0 v1 = coe du_isRelMonomorphism_214 v1
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaMonomorphism.cong
d_cong_2408 ::
  T_IsMagmaMonomorphism_194 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2408 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184 (coe d_isMagmaHomomorphism_202 (coe v0)))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaHomomorphism
d_IsMagmaHomomorphism_2412 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaIsomorphism
d_IsMagmaIsomorphism_2414 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaMonomorphism
d_IsMagmaMonomorphism_2416 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaHomomorphism.homo
d_homo_2420 ::
  T_IsMagmaHomomorphism_176 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2420 v0 = coe d_homo_186 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaHomomorphism.isRelHomomorphism
d_isRelHomomorphism_2422 ::
  T_IsMagmaHomomorphism_176 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2422 v0 = coe d_isRelHomomorphism_184 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaHomomorphism.cong
d_cong_2424 ::
  T_IsMagmaHomomorphism_176 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2424 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe d_isRelHomomorphism_184 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaIsomorphism.homo
d_homo_2428 ::
  T_IsMagmaIsomorphism_218 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2428 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_202 (coe d_isMagmaMonomorphism_226 (coe v0)))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaIsomorphism.injective
d_injective_2430 ::
  T_IsMagmaIsomorphism_218 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_2430 v0
  = coe d_injective_204 (coe d_isMagmaMonomorphism_226 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaIsomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_2432 ::
  T_IsMagmaIsomorphism_218 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_2432 v0
  = coe
      d_isMagmaHomomorphism_202 (coe d_isMagmaMonomorphism_226 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaIsomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_2434 ::
  T_IsMagmaIsomorphism_218 -> T_IsMagmaMonomorphism_194
d_isMagmaMonomorphism_2434 v0
  = coe d_isMagmaMonomorphism_226 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaIsomorphism.isRelHomomorphism
d_isRelHomomorphism_2436 ::
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2436 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_202 (coe d_isMagmaMonomorphism_226 (coe v0)))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaIsomorphism.isRelIsomorphism
d_isRelIsomorphism_2438 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
d_isRelIsomorphism_2438 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isRelIsomorphism_2438
du_isRelIsomorphism_2438 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
du_isRelIsomorphism_2438 v0 v1 = coe du_isRelIsomorphism_244 v1
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaIsomorphism.isRelMonomorphism
d_isRelMonomorphism_2440 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_2440 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_2440 v7
du_isRelMonomorphism_2440 ::
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_2440 v0
  = coe
      du_isRelMonomorphism_214 (coe d_isMagmaMonomorphism_226 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaIsomorphism.surjective
d_surjective_2442 ::
  T_IsMagmaIsomorphism_218 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_2442 v0 = coe d_surjective_228 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaIsomorphism.cong
d_cong_2444 ::
  T_IsMagmaIsomorphism_218 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2444 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_202
            (coe d_isMagmaMonomorphism_226 (coe v0))))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaMonomorphism.homo
d_homo_2448 ::
  T_IsMagmaMonomorphism_194 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2448 v0
  = coe d_homo_186 (coe d_isMagmaHomomorphism_202 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaMonomorphism.injective
d_injective_2450 ::
  T_IsMagmaMonomorphism_194 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_2450 v0 = coe d_injective_204 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_2452 ::
  T_IsMagmaMonomorphism_194 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_2452 v0
  = coe d_isMagmaHomomorphism_202 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaMonomorphism.isRelHomomorphism
d_isRelHomomorphism_2454 ::
  T_IsMagmaMonomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2454 v0
  = coe
      d_isRelHomomorphism_184 (coe d_isMagmaHomomorphism_202 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaMonomorphism.isRelMonomorphism
d_isRelMonomorphism_2456 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_2456 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isRelMonomorphism_2456
du_isRelMonomorphism_2456 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_2456 v0 v1 = coe du_isRelMonomorphism_214 v1
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaMonomorphism.cong
d_cong_2458 ::
  T_IsMagmaMonomorphism_194 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2458 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184 (coe d_isMagmaHomomorphism_202 (coe v0)))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaHomomorphism
d_IsMagmaHomomorphism_2462 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaIsomorphism
d_IsMagmaIsomorphism_2464 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaMonomorphism
d_IsMagmaMonomorphism_2466 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaHomomorphism.homo
d_homo_2470 ::
  T_IsMagmaHomomorphism_176 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2470 v0 = coe d_homo_186 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaHomomorphism.isRelHomomorphism
d_isRelHomomorphism_2472 ::
  T_IsMagmaHomomorphism_176 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2472 v0 = coe d_isRelHomomorphism_184 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaHomomorphism.cong
d_cong_2474 ::
  T_IsMagmaHomomorphism_176 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2474 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe d_isRelHomomorphism_184 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaIsomorphism.homo
d_homo_2478 ::
  T_IsMagmaIsomorphism_218 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2478 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_202 (coe d_isMagmaMonomorphism_226 (coe v0)))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaIsomorphism.injective
d_injective_2480 ::
  T_IsMagmaIsomorphism_218 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_2480 v0
  = coe d_injective_204 (coe d_isMagmaMonomorphism_226 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaIsomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_2482 ::
  T_IsMagmaIsomorphism_218 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_2482 v0
  = coe
      d_isMagmaHomomorphism_202 (coe d_isMagmaMonomorphism_226 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaIsomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_2484 ::
  T_IsMagmaIsomorphism_218 -> T_IsMagmaMonomorphism_194
d_isMagmaMonomorphism_2484 v0
  = coe d_isMagmaMonomorphism_226 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaIsomorphism.isRelHomomorphism
d_isRelHomomorphism_2486 ::
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2486 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_202 (coe d_isMagmaMonomorphism_226 (coe v0)))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaIsomorphism.isRelIsomorphism
d_isRelIsomorphism_2488 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
d_isRelIsomorphism_2488 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isRelIsomorphism_2488
du_isRelIsomorphism_2488 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
du_isRelIsomorphism_2488 v0 v1 = coe du_isRelIsomorphism_244 v1
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaIsomorphism.isRelMonomorphism
d_isRelMonomorphism_2490 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_2490 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_2490 v7
du_isRelMonomorphism_2490 ::
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_2490 v0
  = coe
      du_isRelMonomorphism_214 (coe d_isMagmaMonomorphism_226 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaIsomorphism.surjective
d_surjective_2492 ::
  T_IsMagmaIsomorphism_218 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_2492 v0 = coe d_surjective_228 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaIsomorphism.cong
d_cong_2494 ::
  T_IsMagmaIsomorphism_218 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2494 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_202
            (coe d_isMagmaMonomorphism_226 (coe v0))))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaMonomorphism.homo
d_homo_2498 ::
  T_IsMagmaMonomorphism_194 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2498 v0
  = coe d_homo_186 (coe d_isMagmaHomomorphism_202 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaMonomorphism.injective
d_injective_2500 ::
  T_IsMagmaMonomorphism_194 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_2500 v0 = coe d_injective_204 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_2502 ::
  T_IsMagmaMonomorphism_194 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_2502 v0
  = coe d_isMagmaHomomorphism_202 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaMonomorphism.isRelHomomorphism
d_isRelHomomorphism_2504 ::
  T_IsMagmaMonomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2504 v0
  = coe
      d_isRelHomomorphism_184 (coe d_isMagmaHomomorphism_202 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaMonomorphism.isRelMonomorphism
d_isRelMonomorphism_2506 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_2506 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isRelMonomorphism_2506
du_isRelMonomorphism_2506 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_2506 v0 v1 = coe du_isRelMonomorphism_214 v1
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaMonomorphism.cong
d_cong_2508 ::
  T_IsMagmaMonomorphism_194 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2508 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184 (coe d_isMagmaHomomorphism_202 (coe v0)))
-- Algebra.Morphism.Structures.QuasigroupMorphisms._.Homomorphic₂
d_Homomorphic'8322'_2516 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8322'_2516 = erased
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupHomomorphism
d_IsQuasigroupHomomorphism_2522 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsQuasigroupHomomorphism_2522
  = C_IsQuasigroupHomomorphism'46'constructor_50171 MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
                                                    (AgdaAny -> AgdaAny -> AgdaAny)
                                                    (AgdaAny -> AgdaAny -> AgdaAny)
                                                    (AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupHomomorphism.isRelHomomorphism
d_isRelHomomorphism_2534 ::
  T_IsQuasigroupHomomorphism_2522 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2534 v0
  = case coe v0 of
      C_IsQuasigroupHomomorphism'46'constructor_50171 v1 v2 v3 v4
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupHomomorphism.∙-homo
d_'8729''45'homo_2536 ::
  T_IsQuasigroupHomomorphism_2522 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'homo_2536 v0
  = case coe v0 of
      C_IsQuasigroupHomomorphism'46'constructor_50171 v1 v2 v3 v4
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupHomomorphism.\\-homo
d_'92''92''45'homo_2538 ::
  T_IsQuasigroupHomomorphism_2522 -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'homo_2538 v0
  = case coe v0 of
      C_IsQuasigroupHomomorphism'46'constructor_50171 v1 v2 v3 v4
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupHomomorphism.//-homo
d_'47''47''45'homo_2540 ::
  T_IsQuasigroupHomomorphism_2522 -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'homo_2540 v0
  = case coe v0 of
      C_IsQuasigroupHomomorphism'46'constructor_50171 v1 v2 v3 v4
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupHomomorphism._.cong
d_cong_2544 ::
  T_IsQuasigroupHomomorphism_2522 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2544 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe d_isRelHomomorphism_2534 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupHomomorphism.∙-isMagmaHomomorphism
d_'8729''45'isMagmaHomomorphism_2546 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupHomomorphism_2522 -> T_IsMagmaHomomorphism_176
d_'8729''45'isMagmaHomomorphism_2546 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'isMagmaHomomorphism_2546 v7
du_'8729''45'isMagmaHomomorphism_2546 ::
  T_IsQuasigroupHomomorphism_2522 -> T_IsMagmaHomomorphism_176
du_'8729''45'isMagmaHomomorphism_2546 v0
  = coe
      C_IsMagmaHomomorphism'46'constructor_4629
      (coe d_isRelHomomorphism_2534 (coe v0))
      (coe d_'8729''45'homo_2536 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupHomomorphism.\\-isMagmaHomomorphism
d_'92''92''45'isMagmaHomomorphism_2548 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupHomomorphism_2522 -> T_IsMagmaHomomorphism_176
d_'92''92''45'isMagmaHomomorphism_2548 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'92''92''45'isMagmaHomomorphism_2548 v7
du_'92''92''45'isMagmaHomomorphism_2548 ::
  T_IsQuasigroupHomomorphism_2522 -> T_IsMagmaHomomorphism_176
du_'92''92''45'isMagmaHomomorphism_2548 v0
  = coe
      C_IsMagmaHomomorphism'46'constructor_4629
      (coe d_isRelHomomorphism_2534 (coe v0))
      (coe d_'92''92''45'homo_2538 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupHomomorphism.//-isMagmaHomomorphism
d_'47''47''45'isMagmaHomomorphism_2550 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupHomomorphism_2522 -> T_IsMagmaHomomorphism_176
d_'47''47''45'isMagmaHomomorphism_2550 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'47''47''45'isMagmaHomomorphism_2550 v7
du_'47''47''45'isMagmaHomomorphism_2550 ::
  T_IsQuasigroupHomomorphism_2522 -> T_IsMagmaHomomorphism_176
du_'47''47''45'isMagmaHomomorphism_2550 v0
  = coe
      C_IsMagmaHomomorphism'46'constructor_4629
      (coe d_isRelHomomorphism_2534 (coe v0))
      (coe d_'47''47''45'homo_2540 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupMonomorphism
d_IsQuasigroupMonomorphism_2554 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsQuasigroupMonomorphism_2554
  = C_IsQuasigroupMonomorphism'46'constructor_51967 T_IsQuasigroupHomomorphism_2522
                                                    (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupMonomorphism.isQuasigroupHomomorphism
d_isQuasigroupHomomorphism_2562 ::
  T_IsQuasigroupMonomorphism_2554 -> T_IsQuasigroupHomomorphism_2522
d_isQuasigroupHomomorphism_2562 v0
  = case coe v0 of
      C_IsQuasigroupMonomorphism'46'constructor_51967 v1 v2 -> coe v1
      _                                                     -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupMonomorphism.injective
d_injective_2564 ::
  T_IsQuasigroupMonomorphism_2554 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_2564 v0
  = case coe v0 of
      C_IsQuasigroupMonomorphism'46'constructor_51967 v1 v2 -> coe v2
      _                                                     -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupMonomorphism._.//-homo
d_'47''47''45'homo_2568 ::
  T_IsQuasigroupMonomorphism_2554 -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'homo_2568 v0
  = coe
      d_'47''47''45'homo_2540
      (coe d_isQuasigroupHomomorphism_2562 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupMonomorphism._.//-isMagmaHomomorphism
d_'47''47''45'isMagmaHomomorphism_2570 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupMonomorphism_2554 -> T_IsMagmaHomomorphism_176
d_'47''47''45'isMagmaHomomorphism_2570 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'47''47''45'isMagmaHomomorphism_2570 v7
du_'47''47''45'isMagmaHomomorphism_2570 ::
  T_IsQuasigroupMonomorphism_2554 -> T_IsMagmaHomomorphism_176
du_'47''47''45'isMagmaHomomorphism_2570 v0
  = coe
      du_'47''47''45'isMagmaHomomorphism_2550
      (coe d_isQuasigroupHomomorphism_2562 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupMonomorphism._.\\-homo
d_'92''92''45'homo_2572 ::
  T_IsQuasigroupMonomorphism_2554 -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'homo_2572 v0
  = coe
      d_'92''92''45'homo_2538
      (coe d_isQuasigroupHomomorphism_2562 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupMonomorphism._.\\-isMagmaHomomorphism
d_'92''92''45'isMagmaHomomorphism_2574 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupMonomorphism_2554 -> T_IsMagmaHomomorphism_176
d_'92''92''45'isMagmaHomomorphism_2574 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'92''92''45'isMagmaHomomorphism_2574 v7
du_'92''92''45'isMagmaHomomorphism_2574 ::
  T_IsQuasigroupMonomorphism_2554 -> T_IsMagmaHomomorphism_176
du_'92''92''45'isMagmaHomomorphism_2574 v0
  = coe
      du_'92''92''45'isMagmaHomomorphism_2548
      (coe d_isQuasigroupHomomorphism_2562 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupMonomorphism._.isRelHomomorphism
d_isRelHomomorphism_2576 ::
  T_IsQuasigroupMonomorphism_2554 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2576 v0
  = coe
      d_isRelHomomorphism_2534
      (coe d_isQuasigroupHomomorphism_2562 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupMonomorphism._.∙-homo
d_'8729''45'homo_2578 ::
  T_IsQuasigroupMonomorphism_2554 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'homo_2578 v0
  = coe
      d_'8729''45'homo_2536
      (coe d_isQuasigroupHomomorphism_2562 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupMonomorphism._.∙-isMagmaHomomorphism
d_'8729''45'isMagmaHomomorphism_2580 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupMonomorphism_2554 -> T_IsMagmaHomomorphism_176
d_'8729''45'isMagmaHomomorphism_2580 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'isMagmaHomomorphism_2580 v7
du_'8729''45'isMagmaHomomorphism_2580 ::
  T_IsQuasigroupMonomorphism_2554 -> T_IsMagmaHomomorphism_176
du_'8729''45'isMagmaHomomorphism_2580 v0
  = coe
      du_'8729''45'isMagmaHomomorphism_2546
      (coe d_isQuasigroupHomomorphism_2562 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupMonomorphism._.cong
d_cong_2582 ::
  T_IsQuasigroupMonomorphism_2554 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2582 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_2534
         (coe d_isQuasigroupHomomorphism_2562 (coe v0)))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupMonomorphism.∙-isMagmaMonomorphism
d_'8729''45'isMagmaMonomorphism_2584 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupMonomorphism_2554 -> T_IsMagmaMonomorphism_194
d_'8729''45'isMagmaMonomorphism_2584 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'isMagmaMonomorphism_2584 v7
du_'8729''45'isMagmaMonomorphism_2584 ::
  T_IsQuasigroupMonomorphism_2554 -> T_IsMagmaMonomorphism_194
du_'8729''45'isMagmaMonomorphism_2584 v0
  = coe
      C_IsMagmaMonomorphism'46'constructor_5763
      (coe
         du_'8729''45'isMagmaHomomorphism_2546
         (coe d_isQuasigroupHomomorphism_2562 (coe v0)))
      (coe d_injective_2564 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupMonomorphism.\\-isMagmaMonomorphism
d_'92''92''45'isMagmaMonomorphism_2586 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupMonomorphism_2554 -> T_IsMagmaMonomorphism_194
d_'92''92''45'isMagmaMonomorphism_2586 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'92''92''45'isMagmaMonomorphism_2586 v7
du_'92''92''45'isMagmaMonomorphism_2586 ::
  T_IsQuasigroupMonomorphism_2554 -> T_IsMagmaMonomorphism_194
du_'92''92''45'isMagmaMonomorphism_2586 v0
  = coe
      C_IsMagmaMonomorphism'46'constructor_5763
      (coe
         du_'92''92''45'isMagmaHomomorphism_2548
         (coe d_isQuasigroupHomomorphism_2562 (coe v0)))
      (coe d_injective_2564 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupMonomorphism.//-isMagmaMonomorphism
d_'47''47''45'isMagmaMonomorphism_2588 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupMonomorphism_2554 -> T_IsMagmaMonomorphism_194
d_'47''47''45'isMagmaMonomorphism_2588 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'47''47''45'isMagmaMonomorphism_2588 v7
du_'47''47''45'isMagmaMonomorphism_2588 ::
  T_IsQuasigroupMonomorphism_2554 -> T_IsMagmaMonomorphism_194
du_'47''47''45'isMagmaMonomorphism_2588 v0
  = coe
      C_IsMagmaMonomorphism'46'constructor_5763
      (coe
         du_'47''47''45'isMagmaHomomorphism_2550
         (coe d_isQuasigroupHomomorphism_2562 (coe v0)))
      (coe d_injective_2564 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupMonomorphism._.isRelMonomorphism
d_isRelMonomorphism_2592 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupMonomorphism_2554 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_2592 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_2592 v7
du_isRelMonomorphism_2592 ::
  T_IsQuasigroupMonomorphism_2554 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_2592 v0
  = coe
      du_isRelMonomorphism_214
      (coe du_'47''47''45'isMagmaMonomorphism_2588 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism
d_IsQuasigroupIsomorphism_2596 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsQuasigroupIsomorphism_2596
  = C_IsQuasigroupIsomorphism'46'constructor_54087 T_IsQuasigroupMonomorphism_2554
                                                   (AgdaAny ->
                                                    MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism.isQuasigroupMonomorphism
d_isQuasigroupMonomorphism_2604 ::
  T_IsQuasigroupIsomorphism_2596 -> T_IsQuasigroupMonomorphism_2554
d_isQuasigroupMonomorphism_2604 v0
  = case coe v0 of
      C_IsQuasigroupIsomorphism'46'constructor_54087 v1 v2 -> coe v1
      _                                                    -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism.surjective
d_surjective_2606 ::
  T_IsQuasigroupIsomorphism_2596 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_2606 v0
  = case coe v0 of
      C_IsQuasigroupIsomorphism'46'constructor_54087 v1 v2 -> coe v2
      _                                                    -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism._.//-homo
d_'47''47''45'homo_2610 ::
  T_IsQuasigroupIsomorphism_2596 -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'homo_2610 v0
  = coe
      d_'47''47''45'homo_2540
      (coe
         d_isQuasigroupHomomorphism_2562
         (coe d_isQuasigroupMonomorphism_2604 (coe v0)))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism._.//-isMagmaHomomorphism
d_'47''47''45'isMagmaHomomorphism_2612 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2596 -> T_IsMagmaHomomorphism_176
d_'47''47''45'isMagmaHomomorphism_2612 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'47''47''45'isMagmaHomomorphism_2612 v7
du_'47''47''45'isMagmaHomomorphism_2612 ::
  T_IsQuasigroupIsomorphism_2596 -> T_IsMagmaHomomorphism_176
du_'47''47''45'isMagmaHomomorphism_2612 v0
  = let v1 = d_isQuasigroupMonomorphism_2604 (coe v0) in
    coe
      (coe
         du_'47''47''45'isMagmaHomomorphism_2550
         (coe d_isQuasigroupHomomorphism_2562 (coe v1)))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism._.//-isMagmaMonomorphism
d_'47''47''45'isMagmaMonomorphism_2614 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2596 -> T_IsMagmaMonomorphism_194
d_'47''47''45'isMagmaMonomorphism_2614 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'47''47''45'isMagmaMonomorphism_2614 v7
du_'47''47''45'isMagmaMonomorphism_2614 ::
  T_IsQuasigroupIsomorphism_2596 -> T_IsMagmaMonomorphism_194
du_'47''47''45'isMagmaMonomorphism_2614 v0
  = coe
      du_'47''47''45'isMagmaMonomorphism_2588
      (coe d_isQuasigroupMonomorphism_2604 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism._.\\-homo
d_'92''92''45'homo_2616 ::
  T_IsQuasigroupIsomorphism_2596 -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'homo_2616 v0
  = coe
      d_'92''92''45'homo_2538
      (coe
         d_isQuasigroupHomomorphism_2562
         (coe d_isQuasigroupMonomorphism_2604 (coe v0)))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism._.\\-isMagmaHomomorphism
d_'92''92''45'isMagmaHomomorphism_2618 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2596 -> T_IsMagmaHomomorphism_176
d_'92''92''45'isMagmaHomomorphism_2618 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'92''92''45'isMagmaHomomorphism_2618 v7
du_'92''92''45'isMagmaHomomorphism_2618 ::
  T_IsQuasigroupIsomorphism_2596 -> T_IsMagmaHomomorphism_176
du_'92''92''45'isMagmaHomomorphism_2618 v0
  = let v1 = d_isQuasigroupMonomorphism_2604 (coe v0) in
    coe
      (coe
         du_'92''92''45'isMagmaHomomorphism_2548
         (coe d_isQuasigroupHomomorphism_2562 (coe v1)))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism._.\\-isMagmaMonomorphism
d_'92''92''45'isMagmaMonomorphism_2620 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2596 -> T_IsMagmaMonomorphism_194
d_'92''92''45'isMagmaMonomorphism_2620 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'92''92''45'isMagmaMonomorphism_2620 v7
du_'92''92''45'isMagmaMonomorphism_2620 ::
  T_IsQuasigroupIsomorphism_2596 -> T_IsMagmaMonomorphism_194
du_'92''92''45'isMagmaMonomorphism_2620 v0
  = coe
      du_'92''92''45'isMagmaMonomorphism_2586
      (coe d_isQuasigroupMonomorphism_2604 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism._.injective
d_injective_2622 ::
  T_IsQuasigroupIsomorphism_2596 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_2622 v0
  = coe
      d_injective_2564 (coe d_isQuasigroupMonomorphism_2604 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism._.isQuasigroupHomomorphism
d_isQuasigroupHomomorphism_2624 ::
  T_IsQuasigroupIsomorphism_2596 -> T_IsQuasigroupHomomorphism_2522
d_isQuasigroupHomomorphism_2624 v0
  = coe
      d_isQuasigroupHomomorphism_2562
      (coe d_isQuasigroupMonomorphism_2604 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism._.isRelHomomorphism
d_isRelHomomorphism_2626 ::
  T_IsQuasigroupIsomorphism_2596 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2626 v0
  = coe
      d_isRelHomomorphism_2534
      (coe
         d_isQuasigroupHomomorphism_2562
         (coe d_isQuasigroupMonomorphism_2604 (coe v0)))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism._.isRelMonomorphism
d_isRelMonomorphism_2628 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2596 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_2628 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_2628 v7
du_isRelMonomorphism_2628 ::
  T_IsQuasigroupIsomorphism_2596 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_2628 v0
  = let v1 = d_isQuasigroupMonomorphism_2604 (coe v0) in
    coe
      (coe
         du_isRelMonomorphism_214
         (coe du_'47''47''45'isMagmaMonomorphism_2588 (coe v1)))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism._.∙-homo
d_'8729''45'homo_2630 ::
  T_IsQuasigroupIsomorphism_2596 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'homo_2630 v0
  = coe
      d_'8729''45'homo_2536
      (coe
         d_isQuasigroupHomomorphism_2562
         (coe d_isQuasigroupMonomorphism_2604 (coe v0)))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism._.∙-isMagmaHomomorphism
d_'8729''45'isMagmaHomomorphism_2632 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2596 -> T_IsMagmaHomomorphism_176
d_'8729''45'isMagmaHomomorphism_2632 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'isMagmaHomomorphism_2632 v7
du_'8729''45'isMagmaHomomorphism_2632 ::
  T_IsQuasigroupIsomorphism_2596 -> T_IsMagmaHomomorphism_176
du_'8729''45'isMagmaHomomorphism_2632 v0
  = let v1 = d_isQuasigroupMonomorphism_2604 (coe v0) in
    coe
      (coe
         du_'8729''45'isMagmaHomomorphism_2546
         (coe d_isQuasigroupHomomorphism_2562 (coe v1)))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism._.∙-isMagmaMonomorphism
d_'8729''45'isMagmaMonomorphism_2634 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2596 -> T_IsMagmaMonomorphism_194
d_'8729''45'isMagmaMonomorphism_2634 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'isMagmaMonomorphism_2634 v7
du_'8729''45'isMagmaMonomorphism_2634 ::
  T_IsQuasigroupIsomorphism_2596 -> T_IsMagmaMonomorphism_194
du_'8729''45'isMagmaMonomorphism_2634 v0
  = coe
      du_'8729''45'isMagmaMonomorphism_2584
      (coe d_isQuasigroupMonomorphism_2604 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism._.cong
d_cong_2636 ::
  T_IsQuasigroupIsomorphism_2596 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2636 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_2534
         (coe
            d_isQuasigroupHomomorphism_2562
            (coe d_isQuasigroupMonomorphism_2604 (coe v0))))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism.∙-isMagmaIsomorphism
d_'8729''45'isMagmaIsomorphism_2638 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2596 -> T_IsMagmaIsomorphism_218
d_'8729''45'isMagmaIsomorphism_2638 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'isMagmaIsomorphism_2638 v7
du_'8729''45'isMagmaIsomorphism_2638 ::
  T_IsQuasigroupIsomorphism_2596 -> T_IsMagmaIsomorphism_218
du_'8729''45'isMagmaIsomorphism_2638 v0
  = coe
      C_IsMagmaIsomorphism'46'constructor_7199
      (coe
         du_'8729''45'isMagmaMonomorphism_2584
         (coe d_isQuasigroupMonomorphism_2604 (coe v0)))
      (coe d_surjective_2606 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism.\\-isMagmaIsomorphism
d_'92''92''45'isMagmaIsomorphism_2640 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2596 -> T_IsMagmaIsomorphism_218
d_'92''92''45'isMagmaIsomorphism_2640 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                      v7
  = du_'92''92''45'isMagmaIsomorphism_2640 v7
du_'92''92''45'isMagmaIsomorphism_2640 ::
  T_IsQuasigroupIsomorphism_2596 -> T_IsMagmaIsomorphism_218
du_'92''92''45'isMagmaIsomorphism_2640 v0
  = coe
      C_IsMagmaIsomorphism'46'constructor_7199
      (coe
         du_'92''92''45'isMagmaMonomorphism_2586
         (coe d_isQuasigroupMonomorphism_2604 (coe v0)))
      (coe d_surjective_2606 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism.//-isMagmaIsomorphism
d_'47''47''45'isMagmaIsomorphism_2642 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2596 -> T_IsMagmaIsomorphism_218
d_'47''47''45'isMagmaIsomorphism_2642 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                      v7
  = du_'47''47''45'isMagmaIsomorphism_2642 v7
du_'47''47''45'isMagmaIsomorphism_2642 ::
  T_IsQuasigroupIsomorphism_2596 -> T_IsMagmaIsomorphism_218
du_'47''47''45'isMagmaIsomorphism_2642 v0
  = coe
      C_IsMagmaIsomorphism'46'constructor_7199
      (coe
         du_'47''47''45'isMagmaMonomorphism_2588
         (coe d_isQuasigroupMonomorphism_2604 (coe v0)))
      (coe d_surjective_2606 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism._.isRelIsomorphism
d_isRelIsomorphism_2646 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_326 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2596 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
d_isRelIsomorphism_2646 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelIsomorphism_2646 v7
du_isRelIsomorphism_2646 ::
  T_IsQuasigroupIsomorphism_2596 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
du_isRelIsomorphism_2646 v0
  = coe
      du_isRelIsomorphism_244
      (coe du_'47''47''45'isMagmaIsomorphism_2642 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._._≈_
d__'8776'__2670 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__2670 = erased
-- Algebra.Morphism.Structures.LoopMorphisms._.Carrier
d_Carrier_2676 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 -> ()
d_Carrier_2676 = erased
-- Algebra.Morphism.Structures.LoopMorphisms._.ε
d_ε_2682 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 -> AgdaAny
d_ε_2682 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_ε_2682 v4
du_ε_2682 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 -> AgdaAny
du_ε_2682 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d_ε_394 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.Homomorphic₀
d_Homomorphic'8320'_2712 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> ()
d_Homomorphic'8320'_2712 = erased
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupHomomorphism
d_IsQuasigroupHomomorphism_2722 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism
d_IsQuasigroupIsomorphism_2724 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupMonomorphism
d_IsQuasigroupMonomorphism_2726 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaHomomorphism
d_IsMagmaHomomorphism_2730 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaIsomorphism
d_IsMagmaIsomorphism_2732 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaMonomorphism
d_IsMagmaMonomorphism_2734 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaHomomorphism.homo
d_homo_2738 ::
  T_IsMagmaHomomorphism_176 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2738 v0 = coe d_homo_186 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaHomomorphism.isRelHomomorphism
d_isRelHomomorphism_2740 ::
  T_IsMagmaHomomorphism_176 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2740 v0 = coe d_isRelHomomorphism_184 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaHomomorphism.cong
d_cong_2742 ::
  T_IsMagmaHomomorphism_176 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2742 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe d_isRelHomomorphism_184 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaIsomorphism.homo
d_homo_2746 ::
  T_IsMagmaIsomorphism_218 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2746 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_202 (coe d_isMagmaMonomorphism_226 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaIsomorphism.injective
d_injective_2748 ::
  T_IsMagmaIsomorphism_218 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_2748 v0
  = coe d_injective_204 (coe d_isMagmaMonomorphism_226 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaIsomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_2750 ::
  T_IsMagmaIsomorphism_218 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_2750 v0
  = coe
      d_isMagmaHomomorphism_202 (coe d_isMagmaMonomorphism_226 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaIsomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_2752 ::
  T_IsMagmaIsomorphism_218 -> T_IsMagmaMonomorphism_194
d_isMagmaMonomorphism_2752 v0
  = coe d_isMagmaMonomorphism_226 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaIsomorphism.isRelHomomorphism
d_isRelHomomorphism_2754 ::
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2754 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_202 (coe d_isMagmaMonomorphism_226 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaIsomorphism.isRelIsomorphism
d_isRelIsomorphism_2756 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
d_isRelIsomorphism_2756 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isRelIsomorphism_2756
du_isRelIsomorphism_2756 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
du_isRelIsomorphism_2756 v0 v1 = coe du_isRelIsomorphism_244 v1
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaIsomorphism.isRelMonomorphism
d_isRelMonomorphism_2758 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_2758 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_2758 v7
du_isRelMonomorphism_2758 ::
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_2758 v0
  = coe
      du_isRelMonomorphism_214 (coe d_isMagmaMonomorphism_226 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaIsomorphism.surjective
d_surjective_2760 ::
  T_IsMagmaIsomorphism_218 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_2760 v0 = coe d_surjective_228 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaIsomorphism.cong
d_cong_2762 ::
  T_IsMagmaIsomorphism_218 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2762 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_202
            (coe d_isMagmaMonomorphism_226 (coe v0))))
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaMonomorphism.homo
d_homo_2766 ::
  T_IsMagmaMonomorphism_194 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2766 v0
  = coe d_homo_186 (coe d_isMagmaHomomorphism_202 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaMonomorphism.injective
d_injective_2768 ::
  T_IsMagmaMonomorphism_194 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_2768 v0 = coe d_injective_204 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_2770 ::
  T_IsMagmaMonomorphism_194 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_2770 v0
  = coe d_isMagmaHomomorphism_202 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaMonomorphism.isRelHomomorphism
d_isRelHomomorphism_2772 ::
  T_IsMagmaMonomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2772 v0
  = coe
      d_isRelHomomorphism_184 (coe d_isMagmaHomomorphism_202 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaMonomorphism.isRelMonomorphism
d_isRelMonomorphism_2774 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_2774 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isRelMonomorphism_2774
du_isRelMonomorphism_2774 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_2774 v0 v1 = coe du_isRelMonomorphism_214 v1
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaMonomorphism.cong
d_cong_2776 ::
  T_IsMagmaMonomorphism_194 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2776 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184 (coe d_isMagmaHomomorphism_202 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupHomomorphism.//-homo
d_'47''47''45'homo_2780 ::
  T_IsQuasigroupHomomorphism_2522 -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'homo_2780 v0 = coe d_'47''47''45'homo_2540 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupHomomorphism.//-isMagmaHomomorphism
d_'47''47''45'isMagmaHomomorphism_2782 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupHomomorphism_2522 -> T_IsMagmaHomomorphism_176
d_'47''47''45'isMagmaHomomorphism_2782 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'47''47''45'isMagmaHomomorphism_2782
du_'47''47''45'isMagmaHomomorphism_2782 ::
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupHomomorphism_2522 -> T_IsMagmaHomomorphism_176
du_'47''47''45'isMagmaHomomorphism_2782 v0 v1
  = coe du_'47''47''45'isMagmaHomomorphism_2550 v1
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupHomomorphism.\\-homo
d_'92''92''45'homo_2784 ::
  T_IsQuasigroupHomomorphism_2522 -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'homo_2784 v0 = coe d_'92''92''45'homo_2538 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupHomomorphism.\\-isMagmaHomomorphism
d_'92''92''45'isMagmaHomomorphism_2786 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupHomomorphism_2522 -> T_IsMagmaHomomorphism_176
d_'92''92''45'isMagmaHomomorphism_2786 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'92''92''45'isMagmaHomomorphism_2786
du_'92''92''45'isMagmaHomomorphism_2786 ::
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupHomomorphism_2522 -> T_IsMagmaHomomorphism_176
du_'92''92''45'isMagmaHomomorphism_2786 v0 v1
  = coe du_'92''92''45'isMagmaHomomorphism_2548 v1
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupHomomorphism.isRelHomomorphism
d_isRelHomomorphism_2788 ::
  T_IsQuasigroupHomomorphism_2522 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2788 v0 = coe d_isRelHomomorphism_2534 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupHomomorphism.∙-homo
d_'8729''45'homo_2790 ::
  T_IsQuasigroupHomomorphism_2522 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'homo_2790 v0 = coe d_'8729''45'homo_2536 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupHomomorphism.∙-isMagmaHomomorphism
d_'8729''45'isMagmaHomomorphism_2792 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupHomomorphism_2522 -> T_IsMagmaHomomorphism_176
d_'8729''45'isMagmaHomomorphism_2792 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'8729''45'isMagmaHomomorphism_2792
du_'8729''45'isMagmaHomomorphism_2792 ::
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupHomomorphism_2522 -> T_IsMagmaHomomorphism_176
du_'8729''45'isMagmaHomomorphism_2792 v0 v1
  = coe du_'8729''45'isMagmaHomomorphism_2546 v1
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupHomomorphism.cong
d_cong_2794 ::
  T_IsQuasigroupHomomorphism_2522 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2794 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe d_isRelHomomorphism_2534 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism.//-homo
d_'47''47''45'homo_2798 ::
  T_IsQuasigroupIsomorphism_2596 -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'homo_2798 v0
  = coe
      d_'47''47''45'homo_2540
      (coe
         d_isQuasigroupHomomorphism_2562
         (coe d_isQuasigroupMonomorphism_2604 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism.//-isMagmaHomomorphism
d_'47''47''45'isMagmaHomomorphism_2800 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2596 -> T_IsMagmaHomomorphism_176
d_'47''47''45'isMagmaHomomorphism_2800 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'47''47''45'isMagmaHomomorphism_2800 v7
du_'47''47''45'isMagmaHomomorphism_2800 ::
  T_IsQuasigroupIsomorphism_2596 -> T_IsMagmaHomomorphism_176
du_'47''47''45'isMagmaHomomorphism_2800 v0
  = let v1 = d_isQuasigroupMonomorphism_2604 (coe v0) in
    coe
      (coe
         du_'47''47''45'isMagmaHomomorphism_2550
         (coe d_isQuasigroupHomomorphism_2562 (coe v1)))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism.//-isMagmaIsomorphism
d_'47''47''45'isMagmaIsomorphism_2802 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2596 -> T_IsMagmaIsomorphism_218
d_'47''47''45'isMagmaIsomorphism_2802 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'47''47''45'isMagmaIsomorphism_2802
du_'47''47''45'isMagmaIsomorphism_2802 ::
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2596 -> T_IsMagmaIsomorphism_218
du_'47''47''45'isMagmaIsomorphism_2802 v0 v1
  = coe du_'47''47''45'isMagmaIsomorphism_2642 v1
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism.//-isMagmaMonomorphism
d_'47''47''45'isMagmaMonomorphism_2804 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2596 -> T_IsMagmaMonomorphism_194
d_'47''47''45'isMagmaMonomorphism_2804 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'47''47''45'isMagmaMonomorphism_2804 v7
du_'47''47''45'isMagmaMonomorphism_2804 ::
  T_IsQuasigroupIsomorphism_2596 -> T_IsMagmaMonomorphism_194
du_'47''47''45'isMagmaMonomorphism_2804 v0
  = coe
      du_'47''47''45'isMagmaMonomorphism_2588
      (coe d_isQuasigroupMonomorphism_2604 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism.\\-homo
d_'92''92''45'homo_2806 ::
  T_IsQuasigroupIsomorphism_2596 -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'homo_2806 v0
  = coe
      d_'92''92''45'homo_2538
      (coe
         d_isQuasigroupHomomorphism_2562
         (coe d_isQuasigroupMonomorphism_2604 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism.\\-isMagmaHomomorphism
d_'92''92''45'isMagmaHomomorphism_2808 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2596 -> T_IsMagmaHomomorphism_176
d_'92''92''45'isMagmaHomomorphism_2808 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'92''92''45'isMagmaHomomorphism_2808 v7
du_'92''92''45'isMagmaHomomorphism_2808 ::
  T_IsQuasigroupIsomorphism_2596 -> T_IsMagmaHomomorphism_176
du_'92''92''45'isMagmaHomomorphism_2808 v0
  = let v1 = d_isQuasigroupMonomorphism_2604 (coe v0) in
    coe
      (coe
         du_'92''92''45'isMagmaHomomorphism_2548
         (coe d_isQuasigroupHomomorphism_2562 (coe v1)))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism.\\-isMagmaIsomorphism
d_'92''92''45'isMagmaIsomorphism_2810 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2596 -> T_IsMagmaIsomorphism_218
d_'92''92''45'isMagmaIsomorphism_2810 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'92''92''45'isMagmaIsomorphism_2810
du_'92''92''45'isMagmaIsomorphism_2810 ::
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2596 -> T_IsMagmaIsomorphism_218
du_'92''92''45'isMagmaIsomorphism_2810 v0 v1
  = coe du_'92''92''45'isMagmaIsomorphism_2640 v1
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism.\\-isMagmaMonomorphism
d_'92''92''45'isMagmaMonomorphism_2812 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2596 -> T_IsMagmaMonomorphism_194
d_'92''92''45'isMagmaMonomorphism_2812 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'92''92''45'isMagmaMonomorphism_2812 v7
du_'92''92''45'isMagmaMonomorphism_2812 ::
  T_IsQuasigroupIsomorphism_2596 -> T_IsMagmaMonomorphism_194
du_'92''92''45'isMagmaMonomorphism_2812 v0
  = coe
      du_'92''92''45'isMagmaMonomorphism_2586
      (coe d_isQuasigroupMonomorphism_2604 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism.injective
d_injective_2814 ::
  T_IsQuasigroupIsomorphism_2596 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_2814 v0
  = coe
      d_injective_2564 (coe d_isQuasigroupMonomorphism_2604 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism.isQuasigroupHomomorphism
d_isQuasigroupHomomorphism_2816 ::
  T_IsQuasigroupIsomorphism_2596 -> T_IsQuasigroupHomomorphism_2522
d_isQuasigroupHomomorphism_2816 v0
  = coe
      d_isQuasigroupHomomorphism_2562
      (coe d_isQuasigroupMonomorphism_2604 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism.isQuasigroupMonomorphism
d_isQuasigroupMonomorphism_2818 ::
  T_IsQuasigroupIsomorphism_2596 -> T_IsQuasigroupMonomorphism_2554
d_isQuasigroupMonomorphism_2818 v0
  = coe d_isQuasigroupMonomorphism_2604 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism.isRelHomomorphism
d_isRelHomomorphism_2820 ::
  T_IsQuasigroupIsomorphism_2596 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2820 v0
  = coe
      d_isRelHomomorphism_2534
      (coe
         d_isQuasigroupHomomorphism_2562
         (coe d_isQuasigroupMonomorphism_2604 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism.isRelIsomorphism
d_isRelIsomorphism_2822 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2596 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
d_isRelIsomorphism_2822 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelIsomorphism_2822 v7
du_isRelIsomorphism_2822 ::
  T_IsQuasigroupIsomorphism_2596 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
du_isRelIsomorphism_2822 v0
  = coe
      du_isRelIsomorphism_244
      (coe du_'47''47''45'isMagmaIsomorphism_2642 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism.isRelMonomorphism
d_isRelMonomorphism_2824 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2596 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_2824 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_2824 v7
du_isRelMonomorphism_2824 ::
  T_IsQuasigroupIsomorphism_2596 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_2824 v0
  = let v1 = d_isQuasigroupMonomorphism_2604 (coe v0) in
    coe
      (coe
         du_isRelMonomorphism_214
         (coe du_'47''47''45'isMagmaMonomorphism_2588 (coe v1)))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism.surjective
d_surjective_2826 ::
  T_IsQuasigroupIsomorphism_2596 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_2826 v0 = coe d_surjective_2606 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism.∙-homo
d_'8729''45'homo_2828 ::
  T_IsQuasigroupIsomorphism_2596 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'homo_2828 v0
  = coe
      d_'8729''45'homo_2536
      (coe
         d_isQuasigroupHomomorphism_2562
         (coe d_isQuasigroupMonomorphism_2604 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism.∙-isMagmaHomomorphism
d_'8729''45'isMagmaHomomorphism_2830 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2596 -> T_IsMagmaHomomorphism_176
d_'8729''45'isMagmaHomomorphism_2830 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'isMagmaHomomorphism_2830 v7
du_'8729''45'isMagmaHomomorphism_2830 ::
  T_IsQuasigroupIsomorphism_2596 -> T_IsMagmaHomomorphism_176
du_'8729''45'isMagmaHomomorphism_2830 v0
  = let v1 = d_isQuasigroupMonomorphism_2604 (coe v0) in
    coe
      (coe
         du_'8729''45'isMagmaHomomorphism_2546
         (coe d_isQuasigroupHomomorphism_2562 (coe v1)))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism.∙-isMagmaIsomorphism
d_'8729''45'isMagmaIsomorphism_2832 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2596 -> T_IsMagmaIsomorphism_218
d_'8729''45'isMagmaIsomorphism_2832 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'8729''45'isMagmaIsomorphism_2832
du_'8729''45'isMagmaIsomorphism_2832 ::
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2596 -> T_IsMagmaIsomorphism_218
du_'8729''45'isMagmaIsomorphism_2832 v0 v1
  = coe du_'8729''45'isMagmaIsomorphism_2638 v1
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism.∙-isMagmaMonomorphism
d_'8729''45'isMagmaMonomorphism_2834 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2596 -> T_IsMagmaMonomorphism_194
d_'8729''45'isMagmaMonomorphism_2834 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'isMagmaMonomorphism_2834 v7
du_'8729''45'isMagmaMonomorphism_2834 ::
  T_IsQuasigroupIsomorphism_2596 -> T_IsMagmaMonomorphism_194
du_'8729''45'isMagmaMonomorphism_2834 v0
  = coe
      du_'8729''45'isMagmaMonomorphism_2584
      (coe d_isQuasigroupMonomorphism_2604 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism.cong
d_cong_2836 ::
  T_IsQuasigroupIsomorphism_2596 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2836 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_2534
         (coe
            d_isQuasigroupHomomorphism_2562
            (coe d_isQuasigroupMonomorphism_2604 (coe v0))))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupMonomorphism.//-homo
d_'47''47''45'homo_2840 ::
  T_IsQuasigroupMonomorphism_2554 -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'homo_2840 v0
  = coe
      d_'47''47''45'homo_2540
      (coe d_isQuasigroupHomomorphism_2562 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupMonomorphism.//-isMagmaHomomorphism
d_'47''47''45'isMagmaHomomorphism_2842 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupMonomorphism_2554 -> T_IsMagmaHomomorphism_176
d_'47''47''45'isMagmaHomomorphism_2842 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'47''47''45'isMagmaHomomorphism_2842 v7
du_'47''47''45'isMagmaHomomorphism_2842 ::
  T_IsQuasigroupMonomorphism_2554 -> T_IsMagmaHomomorphism_176
du_'47''47''45'isMagmaHomomorphism_2842 v0
  = coe
      du_'47''47''45'isMagmaHomomorphism_2550
      (coe d_isQuasigroupHomomorphism_2562 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupMonomorphism.//-isMagmaMonomorphism
d_'47''47''45'isMagmaMonomorphism_2844 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupMonomorphism_2554 -> T_IsMagmaMonomorphism_194
d_'47''47''45'isMagmaMonomorphism_2844 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'47''47''45'isMagmaMonomorphism_2844
du_'47''47''45'isMagmaMonomorphism_2844 ::
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupMonomorphism_2554 -> T_IsMagmaMonomorphism_194
du_'47''47''45'isMagmaMonomorphism_2844 v0 v1
  = coe du_'47''47''45'isMagmaMonomorphism_2588 v1
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupMonomorphism.\\-homo
d_'92''92''45'homo_2846 ::
  T_IsQuasigroupMonomorphism_2554 -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'homo_2846 v0
  = coe
      d_'92''92''45'homo_2538
      (coe d_isQuasigroupHomomorphism_2562 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupMonomorphism.\\-isMagmaHomomorphism
d_'92''92''45'isMagmaHomomorphism_2848 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupMonomorphism_2554 -> T_IsMagmaHomomorphism_176
d_'92''92''45'isMagmaHomomorphism_2848 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'92''92''45'isMagmaHomomorphism_2848 v7
du_'92''92''45'isMagmaHomomorphism_2848 ::
  T_IsQuasigroupMonomorphism_2554 -> T_IsMagmaHomomorphism_176
du_'92''92''45'isMagmaHomomorphism_2848 v0
  = coe
      du_'92''92''45'isMagmaHomomorphism_2548
      (coe d_isQuasigroupHomomorphism_2562 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupMonomorphism.\\-isMagmaMonomorphism
d_'92''92''45'isMagmaMonomorphism_2850 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupMonomorphism_2554 -> T_IsMagmaMonomorphism_194
d_'92''92''45'isMagmaMonomorphism_2850 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'92''92''45'isMagmaMonomorphism_2850
du_'92''92''45'isMagmaMonomorphism_2850 ::
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupMonomorphism_2554 -> T_IsMagmaMonomorphism_194
du_'92''92''45'isMagmaMonomorphism_2850 v0 v1
  = coe du_'92''92''45'isMagmaMonomorphism_2586 v1
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupMonomorphism.injective
d_injective_2852 ::
  T_IsQuasigroupMonomorphism_2554 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_2852 v0 = coe d_injective_2564 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupMonomorphism.isQuasigroupHomomorphism
d_isQuasigroupHomomorphism_2854 ::
  T_IsQuasigroupMonomorphism_2554 -> T_IsQuasigroupHomomorphism_2522
d_isQuasigroupHomomorphism_2854 v0
  = coe d_isQuasigroupHomomorphism_2562 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupMonomorphism.isRelHomomorphism
d_isRelHomomorphism_2856 ::
  T_IsQuasigroupMonomorphism_2554 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2856 v0
  = coe
      d_isRelHomomorphism_2534
      (coe d_isQuasigroupHomomorphism_2562 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupMonomorphism.isRelMonomorphism
d_isRelMonomorphism_2858 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupMonomorphism_2554 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_2858 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_2858 v7
du_isRelMonomorphism_2858 ::
  T_IsQuasigroupMonomorphism_2554 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_2858 v0
  = coe
      du_isRelMonomorphism_214
      (coe du_'47''47''45'isMagmaMonomorphism_2588 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupMonomorphism.∙-homo
d_'8729''45'homo_2860 ::
  T_IsQuasigroupMonomorphism_2554 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'homo_2860 v0
  = coe
      d_'8729''45'homo_2536
      (coe d_isQuasigroupHomomorphism_2562 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupMonomorphism.∙-isMagmaHomomorphism
d_'8729''45'isMagmaHomomorphism_2862 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupMonomorphism_2554 -> T_IsMagmaHomomorphism_176
d_'8729''45'isMagmaHomomorphism_2862 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'isMagmaHomomorphism_2862 v7
du_'8729''45'isMagmaHomomorphism_2862 ::
  T_IsQuasigroupMonomorphism_2554 -> T_IsMagmaHomomorphism_176
du_'8729''45'isMagmaHomomorphism_2862 v0
  = coe
      du_'8729''45'isMagmaHomomorphism_2546
      (coe d_isQuasigroupHomomorphism_2562 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupMonomorphism.∙-isMagmaMonomorphism
d_'8729''45'isMagmaMonomorphism_2864 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupMonomorphism_2554 -> T_IsMagmaMonomorphism_194
d_'8729''45'isMagmaMonomorphism_2864 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'8729''45'isMagmaMonomorphism_2864
du_'8729''45'isMagmaMonomorphism_2864 ::
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupMonomorphism_2554 -> T_IsMagmaMonomorphism_194
du_'8729''45'isMagmaMonomorphism_2864 v0 v1
  = coe du_'8729''45'isMagmaMonomorphism_2584 v1
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupMonomorphism.cong
d_cong_2866 ::
  T_IsQuasigroupMonomorphism_2554 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2866 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_2534
         (coe d_isQuasigroupHomomorphism_2562 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaHomomorphism
d_IsMagmaHomomorphism_2870 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaIsomorphism
d_IsMagmaIsomorphism_2872 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaMonomorphism
d_IsMagmaMonomorphism_2874 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaHomomorphism.homo
d_homo_2878 ::
  T_IsMagmaHomomorphism_176 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2878 v0 = coe d_homo_186 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaHomomorphism.isRelHomomorphism
d_isRelHomomorphism_2880 ::
  T_IsMagmaHomomorphism_176 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2880 v0 = coe d_isRelHomomorphism_184 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaHomomorphism.cong
d_cong_2882 ::
  T_IsMagmaHomomorphism_176 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2882 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe d_isRelHomomorphism_184 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaIsomorphism.homo
d_homo_2886 ::
  T_IsMagmaIsomorphism_218 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2886 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_202 (coe d_isMagmaMonomorphism_226 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaIsomorphism.injective
d_injective_2888 ::
  T_IsMagmaIsomorphism_218 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_2888 v0
  = coe d_injective_204 (coe d_isMagmaMonomorphism_226 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaIsomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_2890 ::
  T_IsMagmaIsomorphism_218 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_2890 v0
  = coe
      d_isMagmaHomomorphism_202 (coe d_isMagmaMonomorphism_226 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaIsomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_2892 ::
  T_IsMagmaIsomorphism_218 -> T_IsMagmaMonomorphism_194
d_isMagmaMonomorphism_2892 v0
  = coe d_isMagmaMonomorphism_226 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaIsomorphism.isRelHomomorphism
d_isRelHomomorphism_2894 ::
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2894 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_202 (coe d_isMagmaMonomorphism_226 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaIsomorphism.isRelIsomorphism
d_isRelIsomorphism_2896 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
d_isRelIsomorphism_2896 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isRelIsomorphism_2896
du_isRelIsomorphism_2896 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
du_isRelIsomorphism_2896 v0 v1 = coe du_isRelIsomorphism_244 v1
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaIsomorphism.isRelMonomorphism
d_isRelMonomorphism_2898 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_2898 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_2898 v7
du_isRelMonomorphism_2898 ::
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_2898 v0
  = coe
      du_isRelMonomorphism_214 (coe d_isMagmaMonomorphism_226 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaIsomorphism.surjective
d_surjective_2900 ::
  T_IsMagmaIsomorphism_218 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_2900 v0 = coe d_surjective_228 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaIsomorphism.cong
d_cong_2902 ::
  T_IsMagmaIsomorphism_218 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2902 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_202
            (coe d_isMagmaMonomorphism_226 (coe v0))))
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaMonomorphism.homo
d_homo_2906 ::
  T_IsMagmaMonomorphism_194 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2906 v0
  = coe d_homo_186 (coe d_isMagmaHomomorphism_202 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaMonomorphism.injective
d_injective_2908 ::
  T_IsMagmaMonomorphism_194 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_2908 v0 = coe d_injective_204 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_2910 ::
  T_IsMagmaMonomorphism_194 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_2910 v0
  = coe d_isMagmaHomomorphism_202 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaMonomorphism.isRelHomomorphism
d_isRelHomomorphism_2912 ::
  T_IsMagmaMonomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2912 v0
  = coe
      d_isRelHomomorphism_184 (coe d_isMagmaHomomorphism_202 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaMonomorphism.isRelMonomorphism
d_isRelMonomorphism_2914 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_2914 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isRelMonomorphism_2914
du_isRelMonomorphism_2914 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_2914 v0 v1 = coe du_isRelMonomorphism_214 v1
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaMonomorphism.cong
d_cong_2916 ::
  T_IsMagmaMonomorphism_194 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2916 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184 (coe d_isMagmaHomomorphism_202 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaHomomorphism
d_IsMagmaHomomorphism_2920 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaIsomorphism
d_IsMagmaIsomorphism_2922 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaMonomorphism
d_IsMagmaMonomorphism_2924 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaHomomorphism.homo
d_homo_2928 ::
  T_IsMagmaHomomorphism_176 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2928 v0 = coe d_homo_186 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaHomomorphism.isRelHomomorphism
d_isRelHomomorphism_2930 ::
  T_IsMagmaHomomorphism_176 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2930 v0 = coe d_isRelHomomorphism_184 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaHomomorphism.cong
d_cong_2932 ::
  T_IsMagmaHomomorphism_176 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2932 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe d_isRelHomomorphism_184 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaIsomorphism.homo
d_homo_2936 ::
  T_IsMagmaIsomorphism_218 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2936 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_202 (coe d_isMagmaMonomorphism_226 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaIsomorphism.injective
d_injective_2938 ::
  T_IsMagmaIsomorphism_218 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_2938 v0
  = coe d_injective_204 (coe d_isMagmaMonomorphism_226 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaIsomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_2940 ::
  T_IsMagmaIsomorphism_218 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_2940 v0
  = coe
      d_isMagmaHomomorphism_202 (coe d_isMagmaMonomorphism_226 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaIsomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_2942 ::
  T_IsMagmaIsomorphism_218 -> T_IsMagmaMonomorphism_194
d_isMagmaMonomorphism_2942 v0
  = coe d_isMagmaMonomorphism_226 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaIsomorphism.isRelHomomorphism
d_isRelHomomorphism_2944 ::
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2944 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_202 (coe d_isMagmaMonomorphism_226 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaIsomorphism.isRelIsomorphism
d_isRelIsomorphism_2946 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
d_isRelIsomorphism_2946 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isRelIsomorphism_2946
du_isRelIsomorphism_2946 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_94
du_isRelIsomorphism_2946 v0 v1 = coe du_isRelIsomorphism_244 v1
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaIsomorphism.isRelMonomorphism
d_isRelMonomorphism_2948 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_2948 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_2948 v7
du_isRelMonomorphism_2948 ::
  T_IsMagmaIsomorphism_218 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_2948 v0
  = coe
      du_isRelMonomorphism_214 (coe d_isMagmaMonomorphism_226 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaIsomorphism.surjective
d_surjective_2950 ::
  T_IsMagmaIsomorphism_218 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_2950 v0 = coe d_surjective_228 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaIsomorphism.cong
d_cong_2952 ::
  T_IsMagmaIsomorphism_218 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2952 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_202
            (coe d_isMagmaMonomorphism_226 (coe v0))))
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaMonomorphism.homo
d_homo_2956 ::
  T_IsMagmaMonomorphism_194 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2956 v0
  = coe d_homo_186 (coe d_isMagmaHomomorphism_202 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaMonomorphism.injective
d_injective_2958 ::
  T_IsMagmaMonomorphism_194 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_2958 v0 = coe d_injective_204 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_2960 ::
  T_IsMagmaMonomorphism_194 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_2960 v0
  = coe d_isMagmaHomomorphism_202 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaMonomorphism.isRelHomomorphism
d_isRelHomomorphism_2962 ::
  T_IsMagmaMonomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2962 v0
  = coe
      d_isRelHomomorphism_184 (coe d_isMagmaHomomorphism_202 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaMonomorphism.isRelMonomorphism
d_isRelMonomorphism_2964 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_isRelMonomorphism_2964 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isRelMonomorphism_2964
du_isRelMonomorphism_2964 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
du_isRelMonomorphism_2964 v0 v1 = coe du_isRelMonomorphism_214 v1
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaMonomorphism.cong
d_cong_2966 ::
  T_IsMagmaMonomorphism_194 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2966 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184 (coe d_isMagmaHomomorphism_202 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopHomomorphism
d_IsLoopHomomorphism_2970 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsLoopHomomorphism_2970
  = C_IsLoopHomomorphism'46'constructor_58349 T_IsQuasigroupHomomorphism_2522
                                              AgdaAny
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopHomomorphism.isQuasigroupHomomorphism
d_isQuasigroupHomomorphism_2978 ::
  T_IsLoopHomomorphism_2970 -> T_IsQuasigroupHomomorphism_2522
d_isQuasigroupHomomorphism_2978 v0
  = case coe v0 of
      C_IsLoopHomomorphism'46'constructor_58349 v1 v2 -> coe v1
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopHomomorphism.ε-homo
d_ε'45'homo_2980 :: T_IsLoopHomomorphism_2970 -> AgdaAny
d_ε'45'homo_2980 v0
  = case coe v0 of
      C_IsLoopHomomorphism'46'constructor_58349 v1 v2 -> coe v2
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopHomomorphism._.//-homo
d_'47''47''45'homo_2984 ::
  T_IsLoopHomomorphism_2970 -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'homo_2984 v0
  = coe
      d_'47''47''45'homo_2540
      (coe d_isQuasigroupHomomorphism_2978 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopHomomorphism._.//-isMagmaHomomorphism
d_'47''47''45'isMagmaHomomorphism_2986 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  (AgdaAny -> AgdaAny) ->
  T_IsLoopHomomorphism_2970 -> T_IsMagmaHomomorphism_176
d_'47''47''45'isMagmaHomomorphism_2986 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'47''47''45'isMagmaHomomorphism_2986 v7
du_'47''47''45'isMagmaHomomorphism_2986 ::
  T_IsLoopHomomorphism_2970 -> T_IsMagmaHomomorphism_176
du_'47''47''45'isMagmaHomomorphism_2986 v0
  = coe
      du_'47''47''45'isMagmaHomomorphism_2550
      (coe d_isQuasigroupHomomorphism_2978 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopHomomorphism._.\\-homo
d_'92''92''45'homo_2988 ::
  T_IsLoopHomomorphism_2970 -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'homo_2988 v0
  = coe
      d_'92''92''45'homo_2538
      (coe d_isQuasigroupHomomorphism_2978 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopHomomorphism._.\\-isMagmaHomomorphism
d_'92''92''45'isMagmaHomomorphism_2990 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  (AgdaAny -> AgdaAny) ->
  T_IsLoopHomomorphism_2970 -> T_IsMagmaHomomorphism_176
d_'92''92''45'isMagmaHomomorphism_2990 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'92''92''45'isMagmaHomomorphism_2990 v7
du_'92''92''45'isMagmaHomomorphism_2990 ::
  T_IsLoopHomomorphism_2970 -> T_IsMagmaHomomorphism_176
du_'92''92''45'isMagmaHomomorphism_2990 v0
  = coe
      du_'92''92''45'isMagmaHomomorphism_2548
      (coe d_isQuasigroupHomomorphism_2978 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopHomomorphism._.isRelHomomorphism
d_isRelHomomorphism_2992 ::
  T_IsLoopHomomorphism_2970 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2992 v0
  = coe
      d_isRelHomomorphism_2534
      (coe d_isQuasigroupHomomorphism_2978 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopHomomorphism._.∙-homo
d_'8729''45'homo_2994 ::
  T_IsLoopHomomorphism_2970 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'homo_2994 v0
  = coe
      d_'8729''45'homo_2536
      (coe d_isQuasigroupHomomorphism_2978 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopHomomorphism._.∙-isMagmaHomomorphism
d_'8729''45'isMagmaHomomorphism_2996 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  (AgdaAny -> AgdaAny) ->
  T_IsLoopHomomorphism_2970 -> T_IsMagmaHomomorphism_176
d_'8729''45'isMagmaHomomorphism_2996 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'isMagmaHomomorphism_2996 v7
du_'8729''45'isMagmaHomomorphism_2996 ::
  T_IsLoopHomomorphism_2970 -> T_IsMagmaHomomorphism_176
du_'8729''45'isMagmaHomomorphism_2996 v0
  = coe
      du_'8729''45'isMagmaHomomorphism_2546
      (coe d_isQuasigroupHomomorphism_2978 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopHomomorphism._.cong
d_cong_2998 ::
  T_IsLoopHomomorphism_2970 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2998 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_2534
         (coe d_isQuasigroupHomomorphism_2978 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopMonomorphism
d_IsLoopMonomorphism_3002 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsLoopMonomorphism_3002
  = C_IsLoopMonomorphism'46'constructor_59459 T_IsLoopHomomorphism_2970
                                              (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopMonomorphism.isLoopHomomorphism
d_isLoopHomomorphism_3010 ::
  T_IsLoopMonomorphism_3002 -> T_IsLoopHomomorphism_2970
d_isLoopHomomorphism_3010 v0
  = case coe v0 of
      C_IsLoopMonomorphism'46'constructor_59459 v1 v2 -> coe v1
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopMonomorphism.injective
d_injective_3012 ::
  T_IsLoopMonomorphism_3002 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_3012 v0
  = case coe v0 of
      C_IsLoopMonomorphism'46'constructor_59459 v1 v2 -> coe v2
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopMonomorphism._.//-homo
d_'47''47''45'homo_3016 ::
  T_IsLoopMonomorphism_3002 -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'homo_3016 v0
  = coe
      d_'47''47''45'homo_2540
      (coe
         d_isQuasigroupHomomorphism_2978
         (coe d_isLoopHomomorphism_3010 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopMonomorphism._.//-isMagmaHomomorphism
d_'47''47''45'isMagmaHomomorphism_3018 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  (AgdaAny -> AgdaAny) ->
  T_IsLoopMonomorphism_3002 -> T_IsMagmaHomomorphism_176
d_'47''47''45'isMagmaHomomorphism_3018 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'47''47''45'isMagmaHomomorphism_3018 v7
du_'47''47''45'isMagmaHomomorphism_3018 ::
  T_IsLoopMonomorphism_3002 -> T_IsMagmaHomomorphism_176
du_'47''47''45'isMagmaHomomorphism_3018 v0
  = let v1 = d_isLoopHomomorphism_3010 (coe v0) in
    coe
      (coe
         du_'47''47''45'isMagmaHomomorphism_2550
         (coe d_isQuasigroupHomomorphism_2978 (coe v1)))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopMonomorphism._.\\-homo
d_'92''92''45'homo_3020 ::
  T_IsLoopMonomorphism_3002 -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'homo_3020 v0
  = coe
      d_'92''92''45'homo_2538
      (coe
         d_isQuasigroupHomomorphism_2978
         (coe d_isLoopHomomorphism_3010 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopMonomorphism._.\\-isMagmaHomomorphism
d_'92''92''45'isMagmaHomomorphism_3022 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  (AgdaAny -> AgdaAny) ->
  T_IsLoopMonomorphism_3002 -> T_IsMagmaHomomorphism_176
d_'92''92''45'isMagmaHomomorphism_3022 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'92''92''45'isMagmaHomomorphism_3022 v7
du_'92''92''45'isMagmaHomomorphism_3022 ::
  T_IsLoopMonomorphism_3002 -> T_IsMagmaHomomorphism_176
du_'92''92''45'isMagmaHomomorphism_3022 v0
  = let v1 = d_isLoopHomomorphism_3010 (coe v0) in
    coe
      (coe
         du_'92''92''45'isMagmaHomomorphism_2548
         (coe d_isQuasigroupHomomorphism_2978 (coe v1)))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopMonomorphism._.isQuasigroupHomomorphism
d_isQuasigroupHomomorphism_3024 ::
  T_IsLoopMonomorphism_3002 -> T_IsQuasigroupHomomorphism_2522
d_isQuasigroupHomomorphism_3024 v0
  = coe
      d_isQuasigroupHomomorphism_2978
      (coe d_isLoopHomomorphism_3010 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopMonomorphism._.isRelHomomorphism
d_isRelHomomorphism_3026 ::
  T_IsLoopMonomorphism_3002 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_3026 v0
  = coe
      d_isRelHomomorphism_2534
      (coe
         d_isQuasigroupHomomorphism_2978
         (coe d_isLoopHomomorphism_3010 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopMonomorphism._.ε-homo
d_ε'45'homo_3028 :: T_IsLoopMonomorphism_3002 -> AgdaAny
d_ε'45'homo_3028 v0
  = coe d_ε'45'homo_2980 (coe d_isLoopHomomorphism_3010 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopMonomorphism._.∙-homo
d_'8729''45'homo_3030 ::
  T_IsLoopMonomorphism_3002 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'homo_3030 v0
  = coe
      d_'8729''45'homo_2536
      (coe
         d_isQuasigroupHomomorphism_2978
         (coe d_isLoopHomomorphism_3010 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopMonomorphism._.∙-isMagmaHomomorphism
d_'8729''45'isMagmaHomomorphism_3032 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  (AgdaAny -> AgdaAny) ->
  T_IsLoopMonomorphism_3002 -> T_IsMagmaHomomorphism_176
d_'8729''45'isMagmaHomomorphism_3032 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'isMagmaHomomorphism_3032 v7
du_'8729''45'isMagmaHomomorphism_3032 ::
  T_IsLoopMonomorphism_3002 -> T_IsMagmaHomomorphism_176
du_'8729''45'isMagmaHomomorphism_3032 v0
  = let v1 = d_isLoopHomomorphism_3010 (coe v0) in
    coe
      (coe
         du_'8729''45'isMagmaHomomorphism_2546
         (coe d_isQuasigroupHomomorphism_2978 (coe v1)))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopMonomorphism._.cong
d_cong_3034 ::
  T_IsLoopMonomorphism_3002 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_3034 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_2534
         (coe
            d_isQuasigroupHomomorphism_2978
            (coe d_isLoopHomomorphism_3010 (coe v0))))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopIsomorphism
d_IsLoopIsomorphism_3038 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsLoopIsomorphism_3038
  = C_IsLoopIsomorphism'46'constructor_60703 T_IsLoopMonomorphism_3002
                                             (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopIsomorphism.isLoopMonomorphism
d_isLoopMonomorphism_3046 ::
  T_IsLoopIsomorphism_3038 -> T_IsLoopMonomorphism_3002
d_isLoopMonomorphism_3046 v0
  = case coe v0 of
      C_IsLoopIsomorphism'46'constructor_60703 v1 v2 -> coe v1
      _                                              -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopIsomorphism.surjective
d_surjective_3048 ::
  T_IsLoopIsomorphism_3038 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_3048 v0
  = case coe v0 of
      C_IsLoopIsomorphism'46'constructor_60703 v1 v2 -> coe v2
      _                                              -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopIsomorphism._.//-homo
d_'47''47''45'homo_3052 ::
  T_IsLoopIsomorphism_3038 -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'homo_3052 v0
  = coe
      d_'47''47''45'homo_2540
      (coe
         d_isQuasigroupHomomorphism_2978
         (coe
            d_isLoopHomomorphism_3010
            (coe d_isLoopMonomorphism_3046 (coe v0))))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopIsomorphism._.//-isMagmaHomomorphism
d_'47''47''45'isMagmaHomomorphism_3054 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  (AgdaAny -> AgdaAny) ->
  T_IsLoopIsomorphism_3038 -> T_IsMagmaHomomorphism_176
d_'47''47''45'isMagmaHomomorphism_3054 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'47''47''45'isMagmaHomomorphism_3054 v7
du_'47''47''45'isMagmaHomomorphism_3054 ::
  T_IsLoopIsomorphism_3038 -> T_IsMagmaHomomorphism_176
du_'47''47''45'isMagmaHomomorphism_3054 v0
  = let v1 = d_isLoopMonomorphism_3046 (coe v0) in
    coe
      (let v2 = d_isLoopHomomorphism_3010 (coe v1) in
       coe
         (coe
            du_'47''47''45'isMagmaHomomorphism_2550
            (coe d_isQuasigroupHomomorphism_2978 (coe v2))))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopIsomorphism._.\\-homo
d_'92''92''45'homo_3056 ::
  T_IsLoopIsomorphism_3038 -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'homo_3056 v0
  = coe
      d_'92''92''45'homo_2538
      (coe
         d_isQuasigroupHomomorphism_2978
         (coe
            d_isLoopHomomorphism_3010
            (coe d_isLoopMonomorphism_3046 (coe v0))))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopIsomorphism._.\\-isMagmaHomomorphism
d_'92''92''45'isMagmaHomomorphism_3058 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  (AgdaAny -> AgdaAny) ->
  T_IsLoopIsomorphism_3038 -> T_IsMagmaHomomorphism_176
d_'92''92''45'isMagmaHomomorphism_3058 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'92''92''45'isMagmaHomomorphism_3058 v7
du_'92''92''45'isMagmaHomomorphism_3058 ::
  T_IsLoopIsomorphism_3038 -> T_IsMagmaHomomorphism_176
du_'92''92''45'isMagmaHomomorphism_3058 v0
  = let v1 = d_isLoopMonomorphism_3046 (coe v0) in
    coe
      (let v2 = d_isLoopHomomorphism_3010 (coe v1) in
       coe
         (coe
            du_'92''92''45'isMagmaHomomorphism_2548
            (coe d_isQuasigroupHomomorphism_2978 (coe v2))))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopIsomorphism._.injective
d_injective_3060 ::
  T_IsLoopIsomorphism_3038 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_3060 v0
  = coe d_injective_3012 (coe d_isLoopMonomorphism_3046 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopIsomorphism._.isLoopHomomorphism
d_isLoopHomomorphism_3062 ::
  T_IsLoopIsomorphism_3038 -> T_IsLoopHomomorphism_2970
d_isLoopHomomorphism_3062 v0
  = coe
      d_isLoopHomomorphism_3010 (coe d_isLoopMonomorphism_3046 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopIsomorphism._.isQuasigroupHomomorphism
d_isQuasigroupHomomorphism_3064 ::
  T_IsLoopIsomorphism_3038 -> T_IsQuasigroupHomomorphism_2522
d_isQuasigroupHomomorphism_3064 v0
  = coe
      d_isQuasigroupHomomorphism_2978
      (coe
         d_isLoopHomomorphism_3010 (coe d_isLoopMonomorphism_3046 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopIsomorphism._.isRelHomomorphism
d_isRelHomomorphism_3066 ::
  T_IsLoopIsomorphism_3038 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_3066 v0
  = coe
      d_isRelHomomorphism_2534
      (coe
         d_isQuasigroupHomomorphism_2978
         (coe
            d_isLoopHomomorphism_3010
            (coe d_isLoopMonomorphism_3046 (coe v0))))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopIsomorphism._.ε-homo
d_ε'45'homo_3068 :: T_IsLoopIsomorphism_3038 -> AgdaAny
d_ε'45'homo_3068 v0
  = coe
      d_ε'45'homo_2980
      (coe
         d_isLoopHomomorphism_3010 (coe d_isLoopMonomorphism_3046 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopIsomorphism._.∙-homo
d_'8729''45'homo_3070 ::
  T_IsLoopIsomorphism_3038 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'homo_3070 v0
  = coe
      d_'8729''45'homo_2536
      (coe
         d_isQuasigroupHomomorphism_2978
         (coe
            d_isLoopHomomorphism_3010
            (coe d_isLoopMonomorphism_3046 (coe v0))))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopIsomorphism._.∙-isMagmaHomomorphism
d_'8729''45'isMagmaHomomorphism_3072 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_366 ->
  (AgdaAny -> AgdaAny) ->
  T_IsLoopIsomorphism_3038 -> T_IsMagmaHomomorphism_176
d_'8729''45'isMagmaHomomorphism_3072 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'isMagmaHomomorphism_3072 v7
du_'8729''45'isMagmaHomomorphism_3072 ::
  T_IsLoopIsomorphism_3038 -> T_IsMagmaHomomorphism_176
du_'8729''45'isMagmaHomomorphism_3072 v0
  = let v1 = d_isLoopMonomorphism_3046 (coe v0) in
    coe
      (let v2 = d_isLoopHomomorphism_3010 (coe v1) in
       coe
         (coe
            du_'8729''45'isMagmaHomomorphism_2546
            (coe d_isQuasigroupHomomorphism_2978 (coe v2))))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopIsomorphism._.cong
d_cong_3074 ::
  T_IsLoopIsomorphism_3038 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_3074 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_2534
         (coe
            d_isQuasigroupHomomorphism_2978
            (coe
               d_isLoopHomomorphism_3010
               (coe d_isLoopMonomorphism_3046 (coe v0)))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._._≈_
d__'8776'__3096 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__3096 = erased
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._._⋆
d__'8902'_3100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  AgdaAny -> AgdaAny
d__'8902'_3100 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du__'8902'_3100 v4
du__'8902'_3100 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  AgdaAny -> AgdaAny
du__'8902'_3100 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8902'_440 (coe v0)
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.Carrier
d_Carrier_3114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 -> ()
d_Carrier_3114 = erased
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.Homomorphic₁
d_Homomorphic'8321'_3150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8321'_3150 = erased
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringHomomorphism
d_IsSemiringHomomorphism_3158 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism
d_IsSemiringIsomorphism_3160 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringMonomorphism
d_IsSemiringMonomorphism_3162 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringHomomorphism.*-homo
d_'42''45'homo_3166 ::
  T_IsSemiringHomomorphism_1282 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_3166 v0
  = coe
      d_'42''45'homo_926 (coe d_isNearSemiringHomomorphism_1290 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringHomomorphism.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_3168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringHomomorphism_1282 -> T_IsMagmaHomomorphism_176
d_'42''45'isMagmaHomomorphism_3168 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_3168 v7
du_'42''45'isMagmaHomomorphism_3168 ::
  T_IsSemiringHomomorphism_1282 -> T_IsMagmaHomomorphism_176
du_'42''45'isMagmaHomomorphism_3168 v0
  = coe
      du_'42''45'isMagmaHomomorphism_940
      (coe d_isNearSemiringHomomorphism_1290 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringHomomorphism.*-isMonoidHomomorphism
d_'42''45'isMonoidHomomorphism_3170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringHomomorphism_1282 -> T_IsMonoidHomomorphism_350
d_'42''45'isMonoidHomomorphism_3170 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'42''45'isMonoidHomomorphism_3170
du_'42''45'isMonoidHomomorphism_3170 ::
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringHomomorphism_1282 -> T_IsMonoidHomomorphism_350
du_'42''45'isMonoidHomomorphism_3170 v0 v1
  = coe du_'42''45'isMonoidHomomorphism_1312 v1
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringHomomorphism.homo
d_homo_3172 ::
  T_IsSemiringHomomorphism_1282 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_3172 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_'43''45'isMonoidHomomorphism_924
            (coe d_isNearSemiringHomomorphism_1290 (coe v0))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringHomomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_3174 ::
  T_IsSemiringHomomorphism_1282 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_3174 v0
  = coe
      d_isMagmaHomomorphism_358
      (coe
         d_'43''45'isMonoidHomomorphism_924
         (coe d_isNearSemiringHomomorphism_1290 (coe v0)))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringHomomorphism.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_3176 ::
  T_IsSemiringHomomorphism_1282 -> T_IsMonoidHomomorphism_350
d_'43''45'isMonoidHomomorphism_3176 v0
  = coe
      d_'43''45'isMonoidHomomorphism_924
      (coe d_isNearSemiringHomomorphism_1290 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringHomomorphism.ε-homo
d_ε'45'homo_3178 :: T_IsSemiringHomomorphism_1282 -> AgdaAny
d_ε'45'homo_3178 v0
  = coe
      d_ε'45'homo_360
      (coe
         d_'43''45'isMonoidHomomorphism_924
         (coe d_isNearSemiringHomomorphism_1290 (coe v0)))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringHomomorphism.1#-homo
d_1'35''45'homo_3180 :: T_IsSemiringHomomorphism_1282 -> AgdaAny
d_1'35''45'homo_3180 v0 = coe d_1'35''45'homo_1292 (coe v0)
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringHomomorphism.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_3182 ::
  T_IsSemiringHomomorphism_1282 -> T_IsNearSemiringHomomorphism_916
d_isNearSemiringHomomorphism_3182 v0
  = coe d_isNearSemiringHomomorphism_1290 (coe v0)
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringHomomorphism.isRelHomomorphism
d_isRelHomomorphism_3184 ::
  T_IsSemiringHomomorphism_1282 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_3184 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_'43''45'isMonoidHomomorphism_924
            (coe d_isNearSemiringHomomorphism_1290 (coe v0))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringHomomorphism.cong
d_cong_3186 ::
  T_IsSemiringHomomorphism_1282 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_3186 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe
               d_'43''45'isMonoidHomomorphism_924
               (coe d_isNearSemiringHomomorphism_1290 (coe v0)))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.*-homo
d_'42''45'homo_3190 ::
  T_IsSemiringIsomorphism_1364 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_3190 v0
  = coe
      d_'42''45'homo_926
      (coe
         d_isNearSemiringHomomorphism_1290
         (coe
            d_isSemiringHomomorphism_1324
            (coe d_isSemiringMonomorphism_1372 (coe v0))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_3192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1364 -> T_IsMagmaHomomorphism_176
d_'42''45'isMagmaHomomorphism_3192 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_3192 v7
du_'42''45'isMagmaHomomorphism_3192 ::
  T_IsSemiringIsomorphism_1364 -> T_IsMagmaHomomorphism_176
du_'42''45'isMagmaHomomorphism_3192 v0
  = let v1 = d_isSemiringMonomorphism_1372 (coe v0) in
    coe
      (let v2 = d_isSemiringHomomorphism_1324 (coe v1) in
       coe
         (coe
            du_'42''45'isMagmaHomomorphism_940
            (coe d_isNearSemiringHomomorphism_1290 (coe v2))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.*-isMagmaIsomorphism
d_'42''45'isMagmaIsomorphism_3194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1364 -> T_IsMagmaIsomorphism_218
d_'42''45'isMagmaIsomorphism_3194 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaIsomorphism_3194 v7
du_'42''45'isMagmaIsomorphism_3194 ::
  T_IsSemiringIsomorphism_1364 -> T_IsMagmaIsomorphism_218
du_'42''45'isMagmaIsomorphism_3194 v0
  = coe
      du_'42''45'isMagmaIsomorphism_1036
      (coe du_isNearSemiringIsomorphism_1412 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.*-isMagmaMonomorphism
d_'42''45'isMagmaMonomorphism_3196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1364 -> T_IsMagmaMonomorphism_194
d_'42''45'isMagmaMonomorphism_3196 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaMonomorphism_3196 v7
du_'42''45'isMagmaMonomorphism_3196 ::
  T_IsSemiringIsomorphism_1364 -> T_IsMagmaMonomorphism_194
du_'42''45'isMagmaMonomorphism_3196 v0
  = let v1 = d_isSemiringMonomorphism_1372 (coe v0) in
    coe
      (coe
         du_'42''45'isMagmaMonomorphism_982
         (coe du_isNearSemiringMonomorphism_1352 (coe v1)))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.*-isMonoidHomomorphism
d_'42''45'isMonoidHomomorphism_3198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1364 -> T_IsMonoidHomomorphism_350
d_'42''45'isMonoidHomomorphism_3198 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidHomomorphism_3198 v7
du_'42''45'isMonoidHomomorphism_3198 ::
  T_IsSemiringIsomorphism_1364 -> T_IsMonoidHomomorphism_350
du_'42''45'isMonoidHomomorphism_3198 v0
  = let v1 = d_isSemiringMonomorphism_1372 (coe v0) in
    coe
      (coe
         du_'42''45'isMonoidHomomorphism_1312
         (coe d_isSemiringHomomorphism_1324 (coe v1)))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.*-isMonoidIsomorphism
d_'42''45'isMonoidIsomorphism_3200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1364 -> T_IsMonoidIsomorphism_404
d_'42''45'isMonoidIsomorphism_3200 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'42''45'isMonoidIsomorphism_3200
du_'42''45'isMonoidIsomorphism_3200 ::
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1364 -> T_IsMonoidIsomorphism_404
du_'42''45'isMonoidIsomorphism_3200 v0 v1
  = coe du_'42''45'isMonoidIsomorphism_1420 v1
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.*-isMonoidMonomorphism
d_'42''45'isMonoidMonomorphism_3202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1364 -> T_IsMonoidMonomorphism_372
d_'42''45'isMonoidMonomorphism_3202 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidMonomorphism_3202 v7
du_'42''45'isMonoidMonomorphism_3202 ::
  T_IsSemiringIsomorphism_1364 -> T_IsMonoidMonomorphism_372
du_'42''45'isMonoidMonomorphism_3202 v0
  = coe
      du_'42''45'isMonoidMonomorphism_1360
      (coe d_isSemiringMonomorphism_1372 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.homo
d_homo_3204 ::
  T_IsSemiringIsomorphism_1364 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_3204 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_'43''45'isMonoidHomomorphism_924
            (coe
               d_isNearSemiringHomomorphism_1290
               (coe
                  d_isSemiringHomomorphism_1324
                  (coe d_isSemiringMonomorphism_1372 (coe v0))))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_3206 ::
  T_IsSemiringIsomorphism_1364 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_3206 v0
  = coe
      d_isMagmaHomomorphism_358
      (coe
         d_'43''45'isMonoidHomomorphism_924
         (coe
            d_isNearSemiringHomomorphism_1290
            (coe
               d_isSemiringHomomorphism_1324
               (coe d_isSemiringMonomorphism_1372 (coe v0)))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_3208 ::
  T_IsSemiringIsomorphism_1364 -> T_IsMonoidHomomorphism_350
d_'43''45'isMonoidHomomorphism_3208 v0
  = coe
      d_'43''45'isMonoidHomomorphism_924
      (coe
         d_isNearSemiringHomomorphism_1290
         (coe
            d_isSemiringHomomorphism_1324
            (coe d_isSemiringMonomorphism_1372 (coe v0))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.+-isMonoidIsomorphism
d_'43''45'isMonoidIsomorphism_3210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1364 -> T_IsMonoidIsomorphism_404
d_'43''45'isMonoidIsomorphism_3210 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isMonoidIsomorphism_3210 v7
du_'43''45'isMonoidIsomorphism_3210 ::
  T_IsSemiringIsomorphism_1364 -> T_IsMonoidIsomorphism_404
du_'43''45'isMonoidIsomorphism_3210 v0
  = coe
      du_'43''45'isMonoidIsomorphism_1028
      (coe du_isNearSemiringIsomorphism_1412 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.+-isMonoidMonomorphism
d_'43''45'isMonoidMonomorphism_3212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1364 -> T_IsMonoidMonomorphism_372
d_'43''45'isMonoidMonomorphism_3212 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isMonoidMonomorphism_3212 v7
du_'43''45'isMonoidMonomorphism_3212 ::
  T_IsSemiringIsomorphism_1364 -> T_IsMonoidMonomorphism_372
du_'43''45'isMonoidMonomorphism_3212 v0
  = let v1 = d_isSemiringMonomorphism_1372 (coe v0) in
    coe
      (coe
         du_'43''45'isMonoidMonomorphism_974
         (coe du_isNearSemiringMonomorphism_1352 (coe v1)))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.ε-homo
d_ε'45'homo_3214 :: T_IsSemiringIsomorphism_1364 -> AgdaAny
d_ε'45'homo_3214 v0
  = coe
      d_ε'45'homo_360
      (coe
         d_'43''45'isMonoidHomomorphism_924
         (coe
            d_isNearSemiringHomomorphism_1290
            (coe
               d_isSemiringHomomorphism_1324
               (coe d_isSemiringMonomorphism_1372 (coe v0)))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.1#-homo
d_1'35''45'homo_3216 :: T_IsSemiringIsomorphism_1364 -> AgdaAny
d_1'35''45'homo_3216 v0
  = coe
      d_1'35''45'homo_1292
      (coe
         d_isSemiringHomomorphism_1324
         (coe d_isSemiringMonomorphism_1372 (coe v0)))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.injective
d_injective_3218 ::
  T_IsSemiringIsomorphism_1364 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_3218 v0
  = coe d_injective_1326 (coe d_isSemiringMonomorphism_1372 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_3220 ::
  T_IsSemiringIsomorphism_1364 -> T_IsNearSemiringHomomorphism_916
d_isNearSemiringHomomorphism_3220 v0
  = coe
      d_isNearSemiringHomomorphism_1290
      (coe
         d_isSemiringHomomorphism_1324
         (coe d_isSemiringMonomorphism_1372 (coe v0)))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.isNearSemiringIsomorphism
d_isNearSemiringIsomorphism_3222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1364 -> T_IsNearSemiringIsomorphism_986
d_isNearSemiringIsomorphism_3222 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isNearSemiringIsomorphism_3222
du_isNearSemiringIsomorphism_3222 ::
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1364 -> T_IsNearSemiringIsomorphism_986
du_isNearSemiringIsomorphism_3222 v0 v1
  = coe du_isNearSemiringIsomorphism_1412 v1
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.isNearSemiringMonomorphism
d_isNearSemiringMonomorphism_3224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1364 -> T_IsNearSemiringMonomorphism_944
d_isNearSemiringMonomorphism_3224 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isNearSemiringMonomorphism_3224 v7
du_isNearSemiringMonomorphism_3224 ::
  T_IsSemiringIsomorphism_1364 -> T_IsNearSemiringMonomorphism_944
du_isNearSemiringMonomorphism_3224 v0
  = coe
      du_isNearSemiringMonomorphism_1352
      (coe d_isSemiringMonomorphism_1372 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.isRelHomomorphism
d_isRelHomomorphism_3226 ::
  T_IsSemiringIsomorphism_1364 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_3226 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_'43''45'isMonoidHomomorphism_924
            (coe
               d_isNearSemiringHomomorphism_1290
               (coe
                  d_isSemiringHomomorphism_1324
                  (coe d_isSemiringMonomorphism_1372 (coe v0))))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.isSemiringHomomorphism
d_isSemiringHomomorphism_3228 ::
  T_IsSemiringIsomorphism_1364 -> T_IsSemiringHomomorphism_1282
d_isSemiringHomomorphism_3228 v0
  = coe
      d_isSemiringHomomorphism_1324
      (coe d_isSemiringMonomorphism_1372 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.isSemiringMonomorphism
d_isSemiringMonomorphism_3230 ::
  T_IsSemiringIsomorphism_1364 -> T_IsSemiringMonomorphism_1316
d_isSemiringMonomorphism_3230 v0
  = coe d_isSemiringMonomorphism_1372 (coe v0)
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.surjective
d_surjective_3232 ::
  T_IsSemiringIsomorphism_1364 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_3232 v0 = coe d_surjective_1374 (coe v0)
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.cong
d_cong_3234 ::
  T_IsSemiringIsomorphism_1364 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_3234 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe
               d_'43''45'isMonoidHomomorphism_924
               (coe
                  d_isNearSemiringHomomorphism_1290
                  (coe
                     d_isSemiringHomomorphism_1324
                     (coe d_isSemiringMonomorphism_1372 (coe v0)))))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringMonomorphism.*-homo
d_'42''45'homo_3238 ::
  T_IsSemiringMonomorphism_1316 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_3238 v0
  = coe
      d_'42''45'homo_926
      (coe
         d_isNearSemiringHomomorphism_1290
         (coe d_isSemiringHomomorphism_1324 (coe v0)))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringMonomorphism.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_3240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1316 -> T_IsMagmaHomomorphism_176
d_'42''45'isMagmaHomomorphism_3240 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_3240 v7
du_'42''45'isMagmaHomomorphism_3240 ::
  T_IsSemiringMonomorphism_1316 -> T_IsMagmaHomomorphism_176
du_'42''45'isMagmaHomomorphism_3240 v0
  = let v1 = d_isSemiringHomomorphism_1324 (coe v0) in
    coe
      (coe
         du_'42''45'isMagmaHomomorphism_940
         (coe d_isNearSemiringHomomorphism_1290 (coe v1)))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringMonomorphism.*-isMagmaMonomorphism
d_'42''45'isMagmaMonomorphism_3242 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1316 -> T_IsMagmaMonomorphism_194
d_'42''45'isMagmaMonomorphism_3242 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaMonomorphism_3242 v7
du_'42''45'isMagmaMonomorphism_3242 ::
  T_IsSemiringMonomorphism_1316 -> T_IsMagmaMonomorphism_194
du_'42''45'isMagmaMonomorphism_3242 v0
  = coe
      du_'42''45'isMagmaMonomorphism_982
      (coe du_isNearSemiringMonomorphism_1352 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringMonomorphism.*-isMonoidHomomorphism
d_'42''45'isMonoidHomomorphism_3244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1316 -> T_IsMonoidHomomorphism_350
d_'42''45'isMonoidHomomorphism_3244 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidHomomorphism_3244 v7
du_'42''45'isMonoidHomomorphism_3244 ::
  T_IsSemiringMonomorphism_1316 -> T_IsMonoidHomomorphism_350
du_'42''45'isMonoidHomomorphism_3244 v0
  = coe
      du_'42''45'isMonoidHomomorphism_1312
      (coe d_isSemiringHomomorphism_1324 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringMonomorphism.*-isMonoidMonomorphism
d_'42''45'isMonoidMonomorphism_3246 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1316 -> T_IsMonoidMonomorphism_372
d_'42''45'isMonoidMonomorphism_3246 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'42''45'isMonoidMonomorphism_3246
du_'42''45'isMonoidMonomorphism_3246 ::
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1316 -> T_IsMonoidMonomorphism_372
du_'42''45'isMonoidMonomorphism_3246 v0 v1
  = coe du_'42''45'isMonoidMonomorphism_1360 v1
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringMonomorphism.homo
d_homo_3248 ::
  T_IsSemiringMonomorphism_1316 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_3248 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_'43''45'isMonoidHomomorphism_924
            (coe
               d_isNearSemiringHomomorphism_1290
               (coe d_isSemiringHomomorphism_1324 (coe v0)))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_3250 ::
  T_IsSemiringMonomorphism_1316 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_3250 v0
  = coe
      d_isMagmaHomomorphism_358
      (coe
         d_'43''45'isMonoidHomomorphism_924
         (coe
            d_isNearSemiringHomomorphism_1290
            (coe d_isSemiringHomomorphism_1324 (coe v0))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringMonomorphism.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_3252 ::
  T_IsSemiringMonomorphism_1316 -> T_IsMonoidHomomorphism_350
d_'43''45'isMonoidHomomorphism_3252 v0
  = coe
      d_'43''45'isMonoidHomomorphism_924
      (coe
         d_isNearSemiringHomomorphism_1290
         (coe d_isSemiringHomomorphism_1324 (coe v0)))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringMonomorphism.+-isMonoidMonomorphism
d_'43''45'isMonoidMonomorphism_3254 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1316 -> T_IsMonoidMonomorphism_372
d_'43''45'isMonoidMonomorphism_3254 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isMonoidMonomorphism_3254 v7
du_'43''45'isMonoidMonomorphism_3254 ::
  T_IsSemiringMonomorphism_1316 -> T_IsMonoidMonomorphism_372
du_'43''45'isMonoidMonomorphism_3254 v0
  = coe
      du_'43''45'isMonoidMonomorphism_974
      (coe du_isNearSemiringMonomorphism_1352 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringMonomorphism.ε-homo
d_ε'45'homo_3256 :: T_IsSemiringMonomorphism_1316 -> AgdaAny
d_ε'45'homo_3256 v0
  = coe
      d_ε'45'homo_360
      (coe
         d_'43''45'isMonoidHomomorphism_924
         (coe
            d_isNearSemiringHomomorphism_1290
            (coe d_isSemiringHomomorphism_1324 (coe v0))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringMonomorphism.1#-homo
d_1'35''45'homo_3258 :: T_IsSemiringMonomorphism_1316 -> AgdaAny
d_1'35''45'homo_3258 v0
  = coe
      d_1'35''45'homo_1292 (coe d_isSemiringHomomorphism_1324 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringMonomorphism.injective
d_injective_3260 ::
  T_IsSemiringMonomorphism_1316 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_3260 v0 = coe d_injective_1326 (coe v0)
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringMonomorphism.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_3262 ::
  T_IsSemiringMonomorphism_1316 -> T_IsNearSemiringHomomorphism_916
d_isNearSemiringHomomorphism_3262 v0
  = coe
      d_isNearSemiringHomomorphism_1290
      (coe d_isSemiringHomomorphism_1324 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringMonomorphism.isNearSemiringMonomorphism
d_isNearSemiringMonomorphism_3264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1316 -> T_IsNearSemiringMonomorphism_944
d_isNearSemiringMonomorphism_3264 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isNearSemiringMonomorphism_3264
du_isNearSemiringMonomorphism_3264 ::
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1316 -> T_IsNearSemiringMonomorphism_944
du_isNearSemiringMonomorphism_3264 v0 v1
  = coe du_isNearSemiringMonomorphism_1352 v1
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringMonomorphism.isRelHomomorphism
d_isRelHomomorphism_3266 ::
  T_IsSemiringMonomorphism_1316 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_3266 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_'43''45'isMonoidHomomorphism_924
            (coe
               d_isNearSemiringHomomorphism_1290
               (coe d_isSemiringHomomorphism_1324 (coe v0)))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringMonomorphism.isSemiringHomomorphism
d_isSemiringHomomorphism_3268 ::
  T_IsSemiringMonomorphism_1316 -> T_IsSemiringHomomorphism_1282
d_isSemiringHomomorphism_3268 v0
  = coe d_isSemiringHomomorphism_1324 (coe v0)
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringMonomorphism.cong
d_cong_3270 ::
  T_IsSemiringMonomorphism_1316 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_3270 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe
               d_'43''45'isMonoidHomomorphism_924
               (coe
                  d_isNearSemiringHomomorphism_1290
                  (coe d_isSemiringHomomorphism_1324 (coe v0))))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraHomomorphism
d_IsKleeneAlgebraHomomorphism_3274 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsKleeneAlgebraHomomorphism_3274
  = C_IsKleeneAlgebraHomomorphism'46'constructor_63187 T_IsSemiringHomomorphism_1282
                                                       (AgdaAny -> AgdaAny)
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraHomomorphism.isSemiringHomomorphism
d_isSemiringHomomorphism_3282 ::
  T_IsKleeneAlgebraHomomorphism_3274 -> T_IsSemiringHomomorphism_1282
d_isSemiringHomomorphism_3282 v0
  = case coe v0 of
      C_IsKleeneAlgebraHomomorphism'46'constructor_63187 v1 v2 -> coe v1
      _                                                        -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraHomomorphism.⋆-homo
d_'8902''45'homo_3284 ::
  T_IsKleeneAlgebraHomomorphism_3274 -> AgdaAny -> AgdaAny
d_'8902''45'homo_3284 v0
  = case coe v0 of
      C_IsKleeneAlgebraHomomorphism'46'constructor_63187 v1 v2 -> coe v2
      _                                                        -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraHomomorphism._.*-homo
d_'42''45'homo_3288 ::
  T_IsKleeneAlgebraHomomorphism_3274 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_3288 v0
  = coe
      d_'42''45'homo_926
      (coe
         d_isNearSemiringHomomorphism_1290
         (coe d_isSemiringHomomorphism_3282 (coe v0)))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraHomomorphism._.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_3290 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  (AgdaAny -> AgdaAny) ->
  T_IsKleeneAlgebraHomomorphism_3274 -> T_IsMagmaHomomorphism_176
d_'42''45'isMagmaHomomorphism_3290 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_3290 v7
du_'42''45'isMagmaHomomorphism_3290 ::
  T_IsKleeneAlgebraHomomorphism_3274 -> T_IsMagmaHomomorphism_176
du_'42''45'isMagmaHomomorphism_3290 v0
  = let v1 = d_isSemiringHomomorphism_3282 (coe v0) in
    coe
      (coe
         du_'42''45'isMagmaHomomorphism_940
         (coe d_isNearSemiringHomomorphism_1290 (coe v1)))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraHomomorphism._.*-isMonoidHomomorphism
d_'42''45'isMonoidHomomorphism_3292 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  (AgdaAny -> AgdaAny) ->
  T_IsKleeneAlgebraHomomorphism_3274 -> T_IsMonoidHomomorphism_350
d_'42''45'isMonoidHomomorphism_3292 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidHomomorphism_3292 v7
du_'42''45'isMonoidHomomorphism_3292 ::
  T_IsKleeneAlgebraHomomorphism_3274 -> T_IsMonoidHomomorphism_350
du_'42''45'isMonoidHomomorphism_3292 v0
  = coe
      du_'42''45'isMonoidHomomorphism_1312
      (coe d_isSemiringHomomorphism_3282 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraHomomorphism._.homo
d_homo_3294 ::
  T_IsKleeneAlgebraHomomorphism_3274 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_3294 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_'43''45'isMonoidHomomorphism_924
            (coe
               d_isNearSemiringHomomorphism_1290
               (coe d_isSemiringHomomorphism_3282 (coe v0)))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraHomomorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_3296 ::
  T_IsKleeneAlgebraHomomorphism_3274 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_3296 v0
  = coe
      d_isMagmaHomomorphism_358
      (coe
         d_'43''45'isMonoidHomomorphism_924
         (coe
            d_isNearSemiringHomomorphism_1290
            (coe d_isSemiringHomomorphism_3282 (coe v0))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraHomomorphism._.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_3298 ::
  T_IsKleeneAlgebraHomomorphism_3274 -> T_IsMonoidHomomorphism_350
d_'43''45'isMonoidHomomorphism_3298 v0
  = coe
      d_'43''45'isMonoidHomomorphism_924
      (coe
         d_isNearSemiringHomomorphism_1290
         (coe d_isSemiringHomomorphism_3282 (coe v0)))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraHomomorphism._.ε-homo
d_ε'45'homo_3300 :: T_IsKleeneAlgebraHomomorphism_3274 -> AgdaAny
d_ε'45'homo_3300 v0
  = coe
      d_ε'45'homo_360
      (coe
         d_'43''45'isMonoidHomomorphism_924
         (coe
            d_isNearSemiringHomomorphism_1290
            (coe d_isSemiringHomomorphism_3282 (coe v0))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraHomomorphism._.1#-homo
d_1'35''45'homo_3302 ::
  T_IsKleeneAlgebraHomomorphism_3274 -> AgdaAny
d_1'35''45'homo_3302 v0
  = coe
      d_1'35''45'homo_1292 (coe d_isSemiringHomomorphism_3282 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraHomomorphism._.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_3304 ::
  T_IsKleeneAlgebraHomomorphism_3274 ->
  T_IsNearSemiringHomomorphism_916
d_isNearSemiringHomomorphism_3304 v0
  = coe
      d_isNearSemiringHomomorphism_1290
      (coe d_isSemiringHomomorphism_3282 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraHomomorphism._.isRelHomomorphism
d_isRelHomomorphism_3306 ::
  T_IsKleeneAlgebraHomomorphism_3274 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_3306 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_'43''45'isMonoidHomomorphism_924
            (coe
               d_isNearSemiringHomomorphism_1290
               (coe d_isSemiringHomomorphism_3282 (coe v0)))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraHomomorphism._.cong
d_cong_3308 ::
  T_IsKleeneAlgebraHomomorphism_3274 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_3308 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe
               d_'43''45'isMonoidHomomorphism_924
               (coe
                  d_isNearSemiringHomomorphism_1290
                  (coe d_isSemiringHomomorphism_3282 (coe v0))))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraMonomorphism
d_IsKleeneAlgebraMonomorphism_3312 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsKleeneAlgebraMonomorphism_3312
  = C_IsKleeneAlgebraMonomorphism'46'constructor_64491 T_IsKleeneAlgebraHomomorphism_3274
                                                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraMonomorphism.isKleeneAlgebraHomomorphism
d_isKleeneAlgebraHomomorphism_3320 ::
  T_IsKleeneAlgebraMonomorphism_3312 ->
  T_IsKleeneAlgebraHomomorphism_3274
d_isKleeneAlgebraHomomorphism_3320 v0
  = case coe v0 of
      C_IsKleeneAlgebraMonomorphism'46'constructor_64491 v1 v2 -> coe v1
      _                                                        -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraMonomorphism.injective
d_injective_3322 ::
  T_IsKleeneAlgebraMonomorphism_3312 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_3322 v0
  = case coe v0 of
      C_IsKleeneAlgebraMonomorphism'46'constructor_64491 v1 v2 -> coe v2
      _                                                        -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraMonomorphism._.*-homo
d_'42''45'homo_3326 ::
  T_IsKleeneAlgebraMonomorphism_3312 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_3326 v0
  = coe
      d_'42''45'homo_926
      (coe
         d_isNearSemiringHomomorphism_1290
         (coe
            d_isSemiringHomomorphism_3282
            (coe d_isKleeneAlgebraHomomorphism_3320 (coe v0))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraMonomorphism._.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_3328 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  (AgdaAny -> AgdaAny) ->
  T_IsKleeneAlgebraMonomorphism_3312 -> T_IsMagmaHomomorphism_176
d_'42''45'isMagmaHomomorphism_3328 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_3328 v7
du_'42''45'isMagmaHomomorphism_3328 ::
  T_IsKleeneAlgebraMonomorphism_3312 -> T_IsMagmaHomomorphism_176
du_'42''45'isMagmaHomomorphism_3328 v0
  = let v1 = d_isKleeneAlgebraHomomorphism_3320 (coe v0) in
    coe
      (let v2 = d_isSemiringHomomorphism_3282 (coe v1) in
       coe
         (coe
            du_'42''45'isMagmaHomomorphism_940
            (coe d_isNearSemiringHomomorphism_1290 (coe v2))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraMonomorphism._.*-isMonoidHomomorphism
d_'42''45'isMonoidHomomorphism_3330 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  (AgdaAny -> AgdaAny) ->
  T_IsKleeneAlgebraMonomorphism_3312 -> T_IsMonoidHomomorphism_350
d_'42''45'isMonoidHomomorphism_3330 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidHomomorphism_3330 v7
du_'42''45'isMonoidHomomorphism_3330 ::
  T_IsKleeneAlgebraMonomorphism_3312 -> T_IsMonoidHomomorphism_350
du_'42''45'isMonoidHomomorphism_3330 v0
  = let v1 = d_isKleeneAlgebraHomomorphism_3320 (coe v0) in
    coe
      (coe
         du_'42''45'isMonoidHomomorphism_1312
         (coe d_isSemiringHomomorphism_3282 (coe v1)))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraMonomorphism._.homo
d_homo_3332 ::
  T_IsKleeneAlgebraMonomorphism_3312 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_3332 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_'43''45'isMonoidHomomorphism_924
            (coe
               d_isNearSemiringHomomorphism_1290
               (coe
                  d_isSemiringHomomorphism_3282
                  (coe d_isKleeneAlgebraHomomorphism_3320 (coe v0))))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraMonomorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_3334 ::
  T_IsKleeneAlgebraMonomorphism_3312 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_3334 v0
  = coe
      d_isMagmaHomomorphism_358
      (coe
         d_'43''45'isMonoidHomomorphism_924
         (coe
            d_isNearSemiringHomomorphism_1290
            (coe
               d_isSemiringHomomorphism_3282
               (coe d_isKleeneAlgebraHomomorphism_3320 (coe v0)))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraMonomorphism._.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_3336 ::
  T_IsKleeneAlgebraMonomorphism_3312 -> T_IsMonoidHomomorphism_350
d_'43''45'isMonoidHomomorphism_3336 v0
  = coe
      d_'43''45'isMonoidHomomorphism_924
      (coe
         d_isNearSemiringHomomorphism_1290
         (coe
            d_isSemiringHomomorphism_3282
            (coe d_isKleeneAlgebraHomomorphism_3320 (coe v0))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraMonomorphism._.ε-homo
d_ε'45'homo_3338 :: T_IsKleeneAlgebraMonomorphism_3312 -> AgdaAny
d_ε'45'homo_3338 v0
  = coe
      d_ε'45'homo_360
      (coe
         d_'43''45'isMonoidHomomorphism_924
         (coe
            d_isNearSemiringHomomorphism_1290
            (coe
               d_isSemiringHomomorphism_3282
               (coe d_isKleeneAlgebraHomomorphism_3320 (coe v0)))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraMonomorphism._.1#-homo
d_1'35''45'homo_3340 ::
  T_IsKleeneAlgebraMonomorphism_3312 -> AgdaAny
d_1'35''45'homo_3340 v0
  = coe
      d_1'35''45'homo_1292
      (coe
         d_isSemiringHomomorphism_3282
         (coe d_isKleeneAlgebraHomomorphism_3320 (coe v0)))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraMonomorphism._.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_3342 ::
  T_IsKleeneAlgebraMonomorphism_3312 ->
  T_IsNearSemiringHomomorphism_916
d_isNearSemiringHomomorphism_3342 v0
  = coe
      d_isNearSemiringHomomorphism_1290
      (coe
         d_isSemiringHomomorphism_3282
         (coe d_isKleeneAlgebraHomomorphism_3320 (coe v0)))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraMonomorphism._.isRelHomomorphism
d_isRelHomomorphism_3344 ::
  T_IsKleeneAlgebraMonomorphism_3312 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_3344 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_'43''45'isMonoidHomomorphism_924
            (coe
               d_isNearSemiringHomomorphism_1290
               (coe
                  d_isSemiringHomomorphism_3282
                  (coe d_isKleeneAlgebraHomomorphism_3320 (coe v0))))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraMonomorphism._.isSemiringHomomorphism
d_isSemiringHomomorphism_3346 ::
  T_IsKleeneAlgebraMonomorphism_3312 -> T_IsSemiringHomomorphism_1282
d_isSemiringHomomorphism_3346 v0
  = coe
      d_isSemiringHomomorphism_3282
      (coe d_isKleeneAlgebraHomomorphism_3320 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraMonomorphism._.⋆-homo
d_'8902''45'homo_3348 ::
  T_IsKleeneAlgebraMonomorphism_3312 -> AgdaAny -> AgdaAny
d_'8902''45'homo_3348 v0
  = coe
      d_'8902''45'homo_3284
      (coe d_isKleeneAlgebraHomomorphism_3320 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraMonomorphism._.cong
d_cong_3350 ::
  T_IsKleeneAlgebraMonomorphism_3312 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_3350 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe
               d_'43''45'isMonoidHomomorphism_924
               (coe
                  d_isNearSemiringHomomorphism_1290
                  (coe
                     d_isSemiringHomomorphism_3282
                     (coe d_isKleeneAlgebraHomomorphism_3320 (coe v0)))))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraIsomorphism
d_IsKleeneAlgebraIsomorphism_3354 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsKleeneAlgebraIsomorphism_3354
  = C_IsKleeneAlgebraIsomorphism'46'constructor_65931 T_IsKleeneAlgebraMonomorphism_3312
                                                      (AgdaAny ->
                                                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraIsomorphism.isKleeneAlgebraMonomorphism
d_isKleeneAlgebraMonomorphism_3362 ::
  T_IsKleeneAlgebraIsomorphism_3354 ->
  T_IsKleeneAlgebraMonomorphism_3312
d_isKleeneAlgebraMonomorphism_3362 v0
  = case coe v0 of
      C_IsKleeneAlgebraIsomorphism'46'constructor_65931 v1 v2 -> coe v1
      _                                                       -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraIsomorphism.surjective
d_surjective_3364 ::
  T_IsKleeneAlgebraIsomorphism_3354 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_3364 v0
  = case coe v0 of
      C_IsKleeneAlgebraIsomorphism'46'constructor_65931 v1 v2 -> coe v2
      _                                                       -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraIsomorphism._.*-homo
d_'42''45'homo_3368 ::
  T_IsKleeneAlgebraIsomorphism_3354 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_3368 v0
  = coe
      d_'42''45'homo_926
      (coe
         d_isNearSemiringHomomorphism_1290
         (coe
            d_isSemiringHomomorphism_3282
            (coe
               d_isKleeneAlgebraHomomorphism_3320
               (coe d_isKleeneAlgebraMonomorphism_3362 (coe v0)))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraIsomorphism._.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_3370 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  (AgdaAny -> AgdaAny) ->
  T_IsKleeneAlgebraIsomorphism_3354 -> T_IsMagmaHomomorphism_176
d_'42''45'isMagmaHomomorphism_3370 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_3370 v7
du_'42''45'isMagmaHomomorphism_3370 ::
  T_IsKleeneAlgebraIsomorphism_3354 -> T_IsMagmaHomomorphism_176
du_'42''45'isMagmaHomomorphism_3370 v0
  = let v1 = d_isKleeneAlgebraMonomorphism_3362 (coe v0) in
    coe
      (let v2 = d_isKleeneAlgebraHomomorphism_3320 (coe v1) in
       coe
         (let v3 = d_isSemiringHomomorphism_3282 (coe v2) in
          coe
            (coe
               du_'42''45'isMagmaHomomorphism_940
               (coe d_isNearSemiringHomomorphism_1290 (coe v3)))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraIsomorphism._.*-isMonoidHomomorphism
d_'42''45'isMonoidHomomorphism_3372 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_412 ->
  (AgdaAny -> AgdaAny) ->
  T_IsKleeneAlgebraIsomorphism_3354 -> T_IsMonoidHomomorphism_350
d_'42''45'isMonoidHomomorphism_3372 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidHomomorphism_3372 v7
du_'42''45'isMonoidHomomorphism_3372 ::
  T_IsKleeneAlgebraIsomorphism_3354 -> T_IsMonoidHomomorphism_350
du_'42''45'isMonoidHomomorphism_3372 v0
  = let v1 = d_isKleeneAlgebraMonomorphism_3362 (coe v0) in
    coe
      (let v2 = d_isKleeneAlgebraHomomorphism_3320 (coe v1) in
       coe
         (coe
            du_'42''45'isMonoidHomomorphism_1312
            (coe d_isSemiringHomomorphism_3282 (coe v2))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraIsomorphism._.homo
d_homo_3374 ::
  T_IsKleeneAlgebraIsomorphism_3354 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_3374 v0
  = coe
      d_homo_186
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_'43''45'isMonoidHomomorphism_924
            (coe
               d_isNearSemiringHomomorphism_1290
               (coe
                  d_isSemiringHomomorphism_3282
                  (coe
                     d_isKleeneAlgebraHomomorphism_3320
                     (coe d_isKleeneAlgebraMonomorphism_3362 (coe v0)))))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraIsomorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_3376 ::
  T_IsKleeneAlgebraIsomorphism_3354 -> T_IsMagmaHomomorphism_176
d_isMagmaHomomorphism_3376 v0
  = coe
      d_isMagmaHomomorphism_358
      (coe
         d_'43''45'isMonoidHomomorphism_924
         (coe
            d_isNearSemiringHomomorphism_1290
            (coe
               d_isSemiringHomomorphism_3282
               (coe
                  d_isKleeneAlgebraHomomorphism_3320
                  (coe d_isKleeneAlgebraMonomorphism_3362 (coe v0))))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraIsomorphism._.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_3378 ::
  T_IsKleeneAlgebraIsomorphism_3354 -> T_IsMonoidHomomorphism_350
d_'43''45'isMonoidHomomorphism_3378 v0
  = coe
      d_'43''45'isMonoidHomomorphism_924
      (coe
         d_isNearSemiringHomomorphism_1290
         (coe
            d_isSemiringHomomorphism_3282
            (coe
               d_isKleeneAlgebraHomomorphism_3320
               (coe d_isKleeneAlgebraMonomorphism_3362 (coe v0)))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraIsomorphism._.ε-homo
d_ε'45'homo_3380 :: T_IsKleeneAlgebraIsomorphism_3354 -> AgdaAny
d_ε'45'homo_3380 v0
  = coe
      d_ε'45'homo_360
      (coe
         d_'43''45'isMonoidHomomorphism_924
         (coe
            d_isNearSemiringHomomorphism_1290
            (coe
               d_isSemiringHomomorphism_3282
               (coe
                  d_isKleeneAlgebraHomomorphism_3320
                  (coe d_isKleeneAlgebraMonomorphism_3362 (coe v0))))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraIsomorphism._.1#-homo
d_1'35''45'homo_3382 ::
  T_IsKleeneAlgebraIsomorphism_3354 -> AgdaAny
d_1'35''45'homo_3382 v0
  = coe
      d_1'35''45'homo_1292
      (coe
         d_isSemiringHomomorphism_3282
         (coe
            d_isKleeneAlgebraHomomorphism_3320
            (coe d_isKleeneAlgebraMonomorphism_3362 (coe v0))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraIsomorphism._.injective
d_injective_3384 ::
  T_IsKleeneAlgebraIsomorphism_3354 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_3384 v0
  = coe
      d_injective_3322 (coe d_isKleeneAlgebraMonomorphism_3362 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraIsomorphism._.isKleeneAlgebraHomomorphism
d_isKleeneAlgebraHomomorphism_3386 ::
  T_IsKleeneAlgebraIsomorphism_3354 ->
  T_IsKleeneAlgebraHomomorphism_3274
d_isKleeneAlgebraHomomorphism_3386 v0
  = coe
      d_isKleeneAlgebraHomomorphism_3320
      (coe d_isKleeneAlgebraMonomorphism_3362 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraIsomorphism._.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_3388 ::
  T_IsKleeneAlgebraIsomorphism_3354 ->
  T_IsNearSemiringHomomorphism_916
d_isNearSemiringHomomorphism_3388 v0
  = coe
      d_isNearSemiringHomomorphism_1290
      (coe
         d_isSemiringHomomorphism_3282
         (coe
            d_isKleeneAlgebraHomomorphism_3320
            (coe d_isKleeneAlgebraMonomorphism_3362 (coe v0))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraIsomorphism._.isRelHomomorphism
d_isRelHomomorphism_3390 ::
  T_IsKleeneAlgebraIsomorphism_3354 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_3390 v0
  = coe
      d_isRelHomomorphism_184
      (coe
         d_isMagmaHomomorphism_358
         (coe
            d_'43''45'isMonoidHomomorphism_924
            (coe
               d_isNearSemiringHomomorphism_1290
               (coe
                  d_isSemiringHomomorphism_3282
                  (coe
                     d_isKleeneAlgebraHomomorphism_3320
                     (coe d_isKleeneAlgebraMonomorphism_3362 (coe v0)))))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraIsomorphism._.isSemiringHomomorphism
d_isSemiringHomomorphism_3392 ::
  T_IsKleeneAlgebraIsomorphism_3354 -> T_IsSemiringHomomorphism_1282
d_isSemiringHomomorphism_3392 v0
  = coe
      d_isSemiringHomomorphism_3282
      (coe
         d_isKleeneAlgebraHomomorphism_3320
         (coe d_isKleeneAlgebraMonomorphism_3362 (coe v0)))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraIsomorphism._.⋆-homo
d_'8902''45'homo_3394 ::
  T_IsKleeneAlgebraIsomorphism_3354 -> AgdaAny -> AgdaAny
d_'8902''45'homo_3394 v0
  = coe
      d_'8902''45'homo_3284
      (coe
         d_isKleeneAlgebraHomomorphism_3320
         (coe d_isKleeneAlgebraMonomorphism_3362 (coe v0)))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraIsomorphism._.cong
d_cong_3396 ::
  T_IsKleeneAlgebraIsomorphism_3354 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_3396 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_184
         (coe
            d_isMagmaHomomorphism_358
            (coe
               d_'43''45'isMonoidHomomorphism_924
               (coe
                  d_isNearSemiringHomomorphism_1290
                  (coe
                     d_isSemiringHomomorphism_3282
                     (coe
                        d_isKleeneAlgebraHomomorphism_3320
                        (coe d_isKleeneAlgebraMonomorphism_3362 (coe v0))))))))
